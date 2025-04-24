const std = @import("std");

pub fn RBTree(
    comptime K: type,
    comptime V: type,
    comptime Context: type,
    comptime compareFn: fn (context: Context, a: K, b: K) std.math.Order,
) type {
    return struct {
        pub const Color = enum(u1) {
            red = 0,
            black = 1,
        };

        pub const Node = struct {
            color: Color,
            key: K,
            value: V,
            left: Idx = .sentinel,
            right: Idx = .sentinel,
            parent: Idx = .sentinel,

            const Tree = RBTree(K, V, Context, compareFn);

            pub const Idx = enum(usize) {
                sentinel = std.math.maxInt(usize),
                _,

                pub fn getNext(self: Idx, tree: *const Tree) Idx {
                    const slice = tree.nodes.slice();
                    return slice.items(.parent)[@intFromEnum(self)];
                }

                pub fn setNext(self: Idx, next: Idx, tree: *const Tree) void {
                    const slice = tree.nodes.slice();
                    slice.items(.parent)[@intFromEnum(self)] = next;
                }

                pub fn isFreeSpace(self: Idx) bool {
                    return self != .sentinel;
                }
            };
        };

        pub const InOrderIter = struct {
            tree: *Tree,
            stack: std.ArrayList(Node.Idx),

            const Tree = RBTree(K, V, Context, compareFn);

            pub fn init(
                tree: *Tree,
                allocator: std.mem.Allocator,
            ) !InOrderIter {
                var it: InOrderIter = .{
                    .tree = tree,
                    .stack = try .initCapacity(allocator, tree.nodes.len),
                };
                var node = tree.root;
                const slice = tree.nodes.slice();
                while (node != .sentinel) : (node = slice.items(.left)[@intFromEnum(node)]) {
                    try it.stack.append(node);
                }
                return it;
            }

            pub fn deinit(self: *InOrderIter) void {
                self.stack.deinit();
            }

            pub fn next(self: *InOrderIter) !?Node.Idx {
                if (self.stack.items.len == 0) return null;
                const idx = self.stack.pop() orelse return null;
                const slice = self.tree.nodes.slice();
                var node = slice.items(.right)[@intFromEnum(idx)];
                while (node != .sentinel) : (node = slice.items(.left)[@intFromEnum(node)]) {
                    try self.stack.append(node);
                }
                return idx;
            }
        };

        pub const PreOrderIter = struct {
            tree: *Tree,
            stack: std.ArrayList(Node.Idx),

            const Tree = RBTree(K, V, Context, compareFn);

            pub fn init(
                tree: *Tree,
                allocator: std.mem.Allocator,
            ) !PreOrderIter {
                var it: PreOrderIter = .{
                    .tree = tree,
                    .stack = try .initCapacity(allocator, tree.nodes.len),
                };
                if (tree.root != .sentinel) {
                    try it.stack.append(tree.root);
                }
                return it;
            }

            pub fn deinit(self: *PreOrderIter) void {
                self.stack.deinit();
            }

            pub fn next(self: *PreOrderIter) !?Node.Idx {
                if (self.stack.items.len == 0) return null;
                const idx = self.stack.pop() orelse return null;
                const slice = self.tree.nodes.slice();
                const right = slice.items(.right)[@intFromEnum(idx)];
                const left = slice.items(.left)[@intFromEnum(idx)];
                if (right != .sentinel) {
                    try self.stack.append(right);
                }
                if (left != .sentinel) {
                    try self.stack.append(left);
                }
                return idx;
            }
        };

        pub const PostOrderIter = struct {
            tree: *Tree,
            stack1: std.ArrayList(Node.Idx),
            stack2: std.ArrayList(Node.Idx),

            const Tree = RBTree(K, V, Context, compareFn);

            pub fn init(
                tree: *Tree,
                allocator: std.mem.Allocator,
            ) !PostOrderIter {
                var it: PostOrderIter = .{
                    .tree = tree,
                    .stack1 = try .initCapacity(allocator, tree.nodes.len),
                    .stack2 = try .initCapacity(allocator, tree.nodes.len),
                };
                if (tree.root != .sentinel) {
                    try it.stack1.append(tree.root);
                }
                const slice = tree.nodes.slice();
                while (it.stack1.pop()) |node| {
                    try it.stack2.append(node);
                    const left = slice.items(.left)[@intFromEnum(node)];
                    const right = slice.items(.right)[@intFromEnum(node)];
                    if (left != .sentinel) {
                        try it.stack1.append(left);
                    }
                    if (right != .sentinel) {
                        try it.stack1.append(right);
                    }
                }
                return it;
            }

            pub fn deinit(self: *PostOrderIter) void {
                self.stack1.deinit();
                self.stack2.deinit();
            }

            pub fn next(self: *PostOrderIter) ?Node.Idx {
                if (self.stack2.items.len == 0) return null;
                return self.stack2.pop();
            }
        };

        nodes: std.MultiArrayList(Node),
        context: Context,
        root: Node.Idx,
        free_list: Node.Idx,

        const Self = @This();

        pub fn init(context: Context) Self {
            return .{
                .root = .sentinel,
                .context = context,
                .nodes = .empty,
                .free_list = .sentinel,
            };
        }

        pub fn deinit(self: *Self, allocator: std.mem.Allocator) void {
            self.nodes.deinit(allocator);
        }

        pub fn preOrderIter(self: *Self, allocator: std.mem.Allocator) !PreOrderIter {
            return try .init(self, allocator);
        }

        pub fn inOrderIter(self: *Self, allocator: std.mem.Allocator) !InOrderIter {
            return try .init(self, allocator);
        }

        pub fn postOrderIter(self: *Self, allocator: std.mem.Allocator) !PostOrderIter {
            return try .init(self, allocator);
        }

        pub fn rotateLeft(tree: *Self, x: Node.Idx) void {
            std.debug.assert(x != .sentinel);

            const x_idx = @intFromEnum(x);
            const slice = tree.nodes.slice();

            const y = slice.items(.right)[x_idx];
            std.debug.assert(y != .sentinel);
            const y_idx = @intFromEnum(y);

            const y_left = slice.items(.left)[y_idx];
            const y_left_idx = @intFromEnum(y_left);

            slice.items(.right)[x_idx] = y_left;
            if (y_left != .sentinel) {
                slice.items(.parent)[y_left_idx] = x;
            }

            const x_parent = slice.items(.parent)[x_idx];
            const x_parent_idx = @intFromEnum(x_parent);
            slice.items(.parent)[y_idx] = x_parent;

            if (x_parent == .sentinel) {
                tree.root = y;
            } else if (x == slice.items(.left)[x_parent_idx]) {
                slice.items(.left)[x_parent_idx] = y;
            } else {
                slice.items(.right)[x_parent_idx] = y;
            }

            slice.items(.left)[y_idx] = x;
            slice.items(.parent)[x_idx] = y;
        }

        pub fn rotateRight(tree: *Self, y: Node.Idx) void {
            std.debug.assert(y != .sentinel);

            const y_idx = @intFromEnum(y);
            const slice = tree.nodes.slice();

            const x = slice.items(.left)[y_idx];
            std.debug.assert(x != .sentinel);
            const x_idx = @intFromEnum(x);

            const x_right = slice.items(.right)[x_idx];
            const x_right_idx = @intFromEnum(x_right);

            slice.items(.left)[y_idx] = x_right;
            if (x_right != .sentinel) {
                slice.items(.parent)[x_right_idx] = y;
            }

            const y_parent = slice.items(.parent)[y_idx];
            const y_parent_idx = @intFromEnum(y_parent);
            slice.items(.parent)[x_idx] = y_parent;

            if (y_parent == .sentinel) {
                tree.root = x;
            } else if (y == slice.items(.left)[y_parent_idx]) {
                slice.items(.left)[y_parent_idx] = x;
            } else {
                slice.items(.right)[y_parent_idx] = x;
            }

            slice.items(.right)[x_idx] = y;
            slice.items(.parent)[y_idx] = x;
        }

        pub fn fixInsert(tree: *Self, z: Node.Idx) void {
            const slice = tree.nodes.slice();
            var current_z = z;

            while (true) {
                const parent = slice.items(.parent)[@intFromEnum(current_z)];
                if (parent == .sentinel or slice.items(.color)[@intFromEnum(parent)] == .black) break;

                const grand = slice.items(.parent)[@intFromEnum(parent)];
                if (grand == .sentinel) break;

                if (parent == slice.items(.left)[@intFromEnum(grand)]) {
                    const u = slice.items(.right)[@intFromEnum(grand)];
                    // Case 1
                    if (u != .sentinel and slice.items(.color)[@intFromEnum(u)] == .red) {
                        slice.items(.color)[@intFromEnum(parent)] = .black;
                        slice.items(.color)[@intFromEnum(u)] = .black;
                        slice.items(.color)[@intFromEnum(grand)] = .red;
                        current_z = grand;
                        continue;
                    }
                    // Case 2
                    if (current_z == slice.items(.right)[@intFromEnum(parent)]) {
                        current_z = parent;
                        tree.rotateLeft(current_z);
                    }
                    // Case 3
                    const parent2 = slice.items(.parent)[@intFromEnum(current_z)];
                    slice.items(.color)[@intFromEnum(parent2)] = .black;
                    const grand2 = slice.items(.parent)[@intFromEnum(parent2)];
                    slice.items(.color)[@intFromEnum(grand2)] = .red;
                    tree.rotateRight(grand2);
                } else {
                    const uncle = slice.items(.left)[@intFromEnum(grand)];
                    // Case 1
                    if (uncle != .sentinel and slice.items(.color)[@intFromEnum(uncle)] == .red) {
                        slice.items(.color)[@intFromEnum(parent)] = .black;
                        slice.items(.color)[@intFromEnum(uncle)] = .black;
                        slice.items(.color)[@intFromEnum(grand)] = .red;
                        current_z = grand;
                        continue;
                    }
                    // Case 2
                    if (current_z == slice.items(.left)[@intFromEnum(parent)]) {
                        current_z = parent;
                        tree.rotateRight(current_z);
                    }
                    // Case 3
                    const parent2 = slice.items(.parent)[@intFromEnum(current_z)];
                    slice.items(.color)[@intFromEnum(parent2)] = .black;
                    const grand2 = slice.items(.parent)[@intFromEnum(parent2)];
                    slice.items(.color)[@intFromEnum(grand2)] = .red;
                    tree.rotateLeft(grand2);
                }
            }

            slice.items(.color)[@intFromEnum(tree.root)] = .black;
        }

        pub fn createNode(tree: *Self, allocator: std.mem.Allocator, key: K, value: V) !Node.Idx {
            const new: Node.Idx = blk: {
                if (tree.free_list.isFreeSpace()) {
                    const space = tree.free_list;
                    tree.free_list = space.getNext(tree);
                    break :blk space;
                } else {
                    break :blk @enumFromInt(try tree.nodes.addOne(allocator));
                }
            };

            tree.nodes.set(@intFromEnum(new), .{
                .key = key,
                .value = value,
                .color = .red,
                .left = .sentinel,
                .right = .sentinel,
                .parent = .sentinel,
            });

            return new;
        }

        pub fn insert(tree: *Self, allocator: std.mem.Allocator, key: K, value: V) !?V {
            var parent: Node.Idx = .sentinel;
            var it: Node.Idx = tree.root;

            const slice = tree.nodes.slice();
            while (it != .sentinel) {
                parent = it;
                const ord = compareFn(tree.context, key, slice.items(.key)[@intFromEnum(it)]);
                switch (ord) {
                    .eq => {
                        const old_val = slice.items(.value)[@intFromEnum(it)];
                        slice.items(.value)[@intFromEnum(it)] = value;
                        return old_val;
                    },
                    .lt => it = slice.items(.left)[@intFromEnum(it)],
                    .gt => it = slice.items(.right)[@intFromEnum(it)],
                }
            }

            const new = try tree.createNode(allocator, key, value);
            const new_slice = tree.nodes.slice();
            new_slice.items(.parent)[@intFromEnum(new)] = parent;

            if (parent == .sentinel) {
                tree.root = new;
            } else {
                const ord = compareFn(tree.context, key, new_slice.items(.key)[@intFromEnum(parent)]);
                switch (ord) {
                    .lt => new_slice.items(.left)[@intFromEnum(parent)] = new,
                    .gt => new_slice.items(.right)[@intFromEnum(parent)] = new,
                    .eq => unreachable,
                }
            }

            tree.fixInsert(new);
            return null;
        }

        pub fn find(tree: *const Self, key: K) ?Node.Idx {
            var it = tree.root;
            const slice = tree.nodes.slice();

            while (it != .sentinel) {
                const i = @intFromEnum(it);
                const node_key = slice.items(.key)[i];
                const ord = compareFn(tree.context, key, node_key);
                switch (ord) {
                    .eq => return it,
                    .lt => it = slice.items(.left)[i],
                    .gt => it = slice.items(.right)[i],
                }
            }
            return null;
        }

        fn transplant(tree: *Self, u: Node.Idx, v: Node.Idx) void {
            const slice = tree.nodes.slice();
            const u_parent = slice.items(.parent)[@intFromEnum(u)];

            if (u_parent == .sentinel) {
                tree.root = v;
            } else if (u == slice.items(.left)[@intFromEnum(u_parent)]) {
                slice.items(.left)[@intFromEnum(u_parent)] = v;
            } else {
                slice.items(.right)[@intFromEnum(u_parent)] = v;
            }

            if (v != .sentinel) {
                slice.items(.parent)[@intFromEnum(v)] = u_parent;
            }
        }

        fn minimum(tree: *Self, node: Node.Idx) Node.Idx {
            const slice = tree.nodes.slice();
            var it = node;
            while (slice.items(.left)[@intFromEnum(it)] != .sentinel) {
                it = slice.items(.left)[@intFromEnum(it)];
            }
            return it;
        }

        fn recycleNode(tree: *Self, node: Node.Idx) void {
            node.setNext(tree.free_list, tree);
            tree.free_list = node;
        }

        pub fn delete(tree: *Self, key: K) !?V {
            const slice = tree.nodes.slice();
            const z = tree.find(key) orelse return null;

            const z_idx = @intFromEnum(z);
            const deleted_value = slice.items(.value)[z_idx];

            var y = z;
            var y_original_color = slice.items(.color)[z_idx];
            var x: Node.Idx = .sentinel;

            if (slice.items(.left)[z_idx] == .sentinel) {
                x = slice.items(.right)[z_idx];
                tree.transplant(z, x);
            } else if (slice.items(.right)[z_idx] == .sentinel) {
                x = slice.items(.left)[z_idx];
                tree.transplant(z, x);
            } else {
                y = tree.minimum(slice.items(.right)[z_idx]);
                const y_idx = @intFromEnum(y);
                y_original_color = slice.items(.color)[y_idx];
                x = slice.items(.right)[y_idx];

                if (slice.items(.parent)[y_idx] == z) {
                    if (x != .sentinel) {
                        slice.items(.parent)[@intFromEnum(x)] = y;
                    }
                } else {
                    tree.transplant(y, x);
                    slice.items(.right)[@intFromEnum(y)] = slice.items(.right)[z_idx];
                    slice.items(.parent)[@intFromEnum(slice.items(.right)[z_idx])] = y;
                }

                tree.transplant(z, y);
                slice.items(.left)[@intFromEnum(y)] = slice.items(.left)[z_idx];
                slice.items(.parent)[@intFromEnum(slice.items(.left)[z_idx])] = y;
                slice.items(.color)[@intFromEnum(y)] = slice.items(.color)[z_idx];
            }

            if (y_original_color == .black) {
                fixDelete(tree, x);
            }

            if (y != z) {
                tree.recycleNode(y);
            } else {
                tree.recycleNode(z);
            }

            return deleted_value;
        }

        fn fixDelete(tree: *Self, x: Node.Idx) void {
            if (x == .sentinel) return;

            const slice = tree.nodes.slice();

            var it = x;
            while (it != tree.root and slice.items(.color)[@intFromEnum(it)] == .black) {
                const parent = slice.items(.parent)[@intFromEnum(it)];
                const parent_idx = @intFromEnum(parent);

                const is_left = it == slice.items(.left)[parent_idx];
                var w = if (is_left) slice.items(.right)[parent_idx] else slice.items(.left)[parent_idx];
                const wi = @intFromEnum(w);

                if (slice.items(.color)[wi] == .red) {
                    // Case 1
                    slice.items(.color)[wi] = .black;
                    slice.items(.color)[parent_idx] = .red;
                    if (is_left) {
                        tree.rotateLeft(parent);
                        w = slice.items(.right)[parent_idx];
                    } else {
                        tree.rotateRight(parent);
                        w = slice.items(.left)[parent_idx];
                    }
                }

                const w_left = slice.items(.left)[@intFromEnum(w)];
                const w_right = slice.items(.right)[@intFromEnum(w)];
                const wl_color = if (w_left != .sentinel) slice.items(.color)[@intFromEnum(w_left)] else .black;
                const wr_color = if (w_right != .sentinel) slice.items(.color)[@intFromEnum(w_right)] else .black;

                if (wl_color == .black and wr_color == .black) {
                    // Case 2
                    slice.items(.color)[@intFromEnum(w)] = .red;
                    it = parent;
                } else {
                    if (is_left and wr_color == .black) {
                        // Case 3 (left + right black)
                        if (w_left != .sentinel) {
                            slice.items(.color)[@intFromEnum(w_left)] = .black;
                        }
                        slice.items(.color)[@intFromEnum(w)] = .red;
                        tree.rotateRight(w);
                        w = slice.items(.right)[parent_idx];
                    } else if (!is_left and wl_color == .black) {
                        // Case 3 (right + left black)
                        if (w_right != .sentinel) {
                            slice.items(.color)[@intFromEnum(w_right)] = .black;
                        }
                        slice.items(.color)[@intFromEnum(w)] = .red;
                        tree.rotateLeft(w);
                        w = slice.items(.left)[parent_idx];
                    }

                    // Case 4
                    slice.items(.color)[@intFromEnum(w)] = slice.items(.color)[parent_idx];
                    slice.items(.color)[parent_idx] = .black;

                    if (is_left) {
                        if (w_right != .sentinel) {
                            slice.items(.color)[@intFromEnum(w_right)] = .black;
                        }
                        tree.rotateLeft(parent);
                    } else {
                        if (w_left != .sentinel) {
                            slice.items(.color)[@intFromEnum(w_left)] = .black;
                        }
                        tree.rotateRight(parent);
                    }
                    break;
                }
            }

            if (it != .sentinel) {
                slice.items(.color)[@intFromEnum(it)] = .black;
            }
        }
    };
}

fn compare(_: void, a: usize, b: usize) std.math.Order {
    return std.math.order(a, b);
}

test "insert, find" {
    const allocator = std.testing.allocator;
    var tree: RBTree(usize, usize, void, compare) = .init({});
    defer tree.deinit(allocator);

    _ = try tree.insert(allocator, 10, 100);
    _ = try tree.insert(allocator, 20, 200);
    _ = try tree.insert(allocator, 30, 300);

    const node10 = tree.find(10).?;
    const node20 = tree.find(20).?;
    const node30 = tree.find(30).?;
    try std.testing.expectEqual(100, tree.nodes.items(.value)[@intFromEnum(node10)]);
    try std.testing.expectEqual(200, tree.nodes.items(.value)[@intFromEnum(node20)]);
    try std.testing.expectEqual(300, tree.nodes.items(.value)[@intFromEnum(node30)]);

    const old_val = try tree.insert(allocator, 20, 250);
    try std.testing.expectEqual(200, old_val.?);
    const updated_node = tree.find(20).?;
    try std.testing.expectEqual(250, tree.nodes.items(.value)[@intFromEnum(updated_node)]);
}

test "delete" {
    const allocator = std.testing.allocator;
    var tree: RBTree(usize, usize, void, compare) = .init({});
    defer tree.deinit(allocator);

    _ = try tree.insert(allocator, 20, 200);
    _ = try tree.insert(allocator, 10, 100);
    _ = try tree.insert(allocator, 30, 300);
    _ = try tree.insert(allocator, 40, 400);
    _ = try tree.insert(allocator, 50, 500);

    const deleted50 = try tree.delete(50);
    try std.testing.expectEqual(500, deleted50.?);
    try std.testing.expectEqual(null, tree.find(50));

    const deleted30 = try tree.delete(30);
    try std.testing.expectEqual(300, deleted30.?);
    try std.testing.expectEqual(null, tree.find(30));

    const deleted20 = try tree.delete(20);
    try std.testing.expectEqual(200, deleted20.?);
    try std.testing.expectEqual(null, tree.find(20));
}

fn checkRBProperties(tree: *const RBTree(usize, usize, void, compare)) bool {
    const slice = tree.nodes.slice();
    if (tree.nodes.len == 0) return true;

    if (slice.items(.color)[@intFromEnum(tree.root)] != .black) return false;

    for (0..tree.nodes.len) |i| {
        if (slice.items(.color)[i] == .red) {
            const left = slice.items(.left)[i];
            const right = slice.items(.right)[i];
            if (left != .sentinel and slice.items(.color)[@intFromEnum(left)] == .red) return false;
            if (right != .sentinel and slice.items(.color)[@intFromEnum(right)] == .red) return false;
        }
    }
    return true;
}

test "color test" {
    const allocator = std.testing.allocator;
    var tree: RBTree(usize, usize, void, compare) = .init({});
    defer tree.deinit(allocator);

    _ = try tree.insert(allocator, 10, 100);
    _ = try tree.insert(allocator, 20, 200);
    _ = try tree.insert(allocator, 30, 300);
    try std.testing.expect(checkRBProperties(&tree));

    _ = try tree.delete(20);
    try std.testing.expect(checkRBProperties(&tree));
}

test "edge case" {
    const allocator = std.testing.allocator;
    var tree: RBTree(usize, usize, void, compare) = .init({});
    defer tree.deinit(allocator);

    const deleted = try tree.delete(10);
    try std.testing.expectEqual(null, deleted);

    _ = try tree.insert(allocator, 10, 100);
    const node = tree.find(10).?;
    try std.testing.expectEqual(100, tree.nodes.items(.value)[@intFromEnum(node)]);
    _ = try tree.delete(10);
    try std.testing.expectEqual(null, tree.find(10));
}

test "mass insert / delete leak check" {
    const allocator = std.testing.allocator;
    var tree: RBTree(usize, void, void, compare) = .init({});
    defer tree.deinit(allocator);

    for (0..1000) |n| _ = try tree.insert(allocator, n, {});
    for (0..1000) |n| _ = try tree.delete(n);

    try std.testing.expect(tree.root == .sentinel);
    try std.testing.expect(tree.nodes.len == 1000);
    try std.testing.expect(tree.free_list != .sentinel);
}

test "free-list reuse sanity" {
    const allocator = std.testing.allocator;
    var tree: RBTree(usize, usize, void, compare) = .init({});
    defer tree.deinit(allocator);

    for (1..4) |k| {
        _ = try tree.insert(allocator, k, k * 10);
    }
    for (1..4) |k| {
        _ = try tree.delete(k);
    }

    const len_after_first_round = tree.nodes.len;
    const freelist_head = tree.free_list;

    try std.testing.expect(len_after_first_round == 3);
    try std.testing.expect(freelist_head != .sentinel);

    for (4..7) |k| {
        _ = try tree.insert(allocator, k, k * 10);
    }

    try std.testing.expect(tree.nodes.len == len_after_first_round);

    try std.testing.expect(tree.free_list != freelist_head);

    for (4..7) |k| {
        const idx = tree.find(k).?;
        try std.testing.expectEqual(k * 10, tree.nodes.items(.value)[@intFromEnum(idx)]);
    }
}

test "fuzz 10 000 mixed ops" {
    const allocator = std.testing.allocator;
    var tree: RBTree(usize, usize, void, compare) = .init({});
    defer tree.deinit(allocator);

    var truth: std.AutoHashMap(usize, usize) = .init(allocator);
    defer truth.deinit();

    var prng: std.Random.DefaultPrng = .init(0xdeadbeef);
    const rnd = prng.random();

    const n_iters = 10_000;

    var insert_count: usize = 0;
    var delete_count: usize = 0;

    for (0..n_iters) |_| {
        const key: usize = rnd.int(usize);
        const is_insert = rnd.boolean();

        if (is_insert) {
            const val = rnd.int(usize);
            const old_tree = try tree.insert(allocator, key, val);
            const old_map = truth.get(key);

            try std.testing.expect(old_tree == old_map);
            try truth.put(key, val);
            insert_count += 1;
        } else {
            const del_tree = try tree.delete(key);
            const del_map_entry = truth.fetchRemove(key);
            const del_map = if (del_map_entry) |e| e.value else null;
            try std.testing.expect(del_tree == del_map);
            delete_count += 1;
        }

        try std.testing.expect(checkRBProperties(&tree));

        var it = truth.iterator();
        while (it.next()) |e| {
            const idx = tree.find(e.key_ptr.*).?;
            try std.testing.expectEqual(e.value_ptr.*, tree.nodes.items(.value)[@intFromEnum(idx)]);
        }

        if (rnd.boolean()) {
            const sample = rnd.int(usize);
            if (!truth.contains(sample)) {
                try std.testing.expect(tree.find(sample) == null);
            }
        }
    }

    std.debug.print("fuzz done: {d} inserts / {d} deletes\n", .{ insert_count, delete_count });
}

test "memory reuse under heavy churn" {
    const allocator = std.testing.allocator;
    var tree: RBTree(usize, usize, void, compare) = .init({});
    defer tree.deinit(allocator);

    const n = 50;
    const rounds = 100;

    for (0..n) |i| {
        _ = try tree.insert(allocator, i, i * 10);
    }
    try std.testing.expect(tree.nodes.len == n);
    try std.testing.expect(tree.free_list == .sentinel);

    for (0..rounds) |_| {
        for (0..n) |i| {
            if (i % 2 != 0) continue;
            _ = try tree.delete(i);
        }
        for (0..n) |i| {
            if (i % 2 != 1) continue;
            _ = try tree.delete(i);
        }

        try std.testing.expect(tree.root == .sentinel);
        try std.testing.expect(tree.nodes.len == n);
        try std.testing.expect(tree.free_list != .sentinel);

        for (0..n) |i| {
            _ = try tree.insert(allocator, i, i * 10);
        }
        try std.testing.expect(tree.nodes.len == n);
        try std.testing.expect(tree.free_list == .sentinel);

        for (0..n) |i| {
            const idx = tree.find(i).?;
            try std.testing.expectEqual(i * 10, tree.nodes.items(.value)[@intFromEnum(idx)]);
        }
    }
}

test "iterator order correctness" {
    const allocator = std.testing.allocator;
    var tree: RBTree(usize, usize, void, compare) = .init({});
    defer tree.deinit(allocator);

    const keys = [_]usize{ 10, 5, 3, 7, 15 };
    for (keys) |k| {
        _ = try tree.insert(allocator, k, k);
    }

    var in_iter = try tree.inOrderIter(allocator);
    defer in_iter.deinit();
    const expected_in = [_]usize{ 3, 5, 7, 10, 15 };
    var i: usize = 0;
    while (try in_iter.next()) |idx| : (i += 1) {
        const k = tree.nodes.items(.key)[@intFromEnum(idx)];
        try std.testing.expectEqual(expected_in[i], k);
    }
    try std.testing.expect(i == expected_in.len);

    var pre_iter = try tree.preOrderIter(allocator);
    defer pre_iter.deinit();
    const expected_pre = [_]usize{ 5, 3, 10, 7, 15 };
    i = 0;
    while (try pre_iter.next()) |idx| : (i += 1) {
        const k = tree.nodes.items(.key)[@intFromEnum(idx)];
        try std.testing.expectEqual(expected_pre[i], k);
    }
    try std.testing.expect(i == expected_pre.len);

    var post_iter = try tree.postOrderIter(allocator);
    defer post_iter.deinit();
    const expected_post = [_]usize{ 3, 7, 15, 10, 5 };
    i = 0;
    while (post_iter.next()) |idx| : (i += 1) {
        const k = tree.nodes.items(.key)[@intFromEnum(idx)];
        try std.testing.expectEqual(expected_post[i], k);
    }
    try std.testing.expect(i == expected_post.len);
}

fn collectInOrder(
    tree: *const RBTree(usize, usize, void, compare),
    node: RBTree(usize, usize, void, compare).Node.Idx,
    out: *std.ArrayList(usize),
) void {
    if (node == .sentinel) return;
    const s = tree.nodes.slice();
    collectInOrder(tree, s.items(.left)[@intFromEnum(node)], out);
    out.appendAssumeCapacity(s.items(.key)[@intFromEnum(node)]);
    collectInOrder(tree, s.items(.right)[@intFromEnum(node)], out);
}

fn collectPreOrder(
    tree: *const RBTree(usize, usize, void, compare),
    node: RBTree(usize, usize, void, compare).Node.Idx,
    out: *std.ArrayList(usize),
) void {
    if (node == .sentinel) return;
    const s = tree.nodes.slice();
    out.appendAssumeCapacity(s.items(.key)[@intFromEnum(node)]);
    collectPreOrder(tree, s.items(.left)[@intFromEnum(node)], out);
    collectPreOrder(tree, s.items(.right)[@intFromEnum(node)], out);
}

fn collectPostOrder(
    tree: *const RBTree(usize, usize, void, compare),
    node: RBTree(usize, usize, void, compare).Node.Idx,
    out: *std.ArrayList(usize),
) void {
    if (node == .sentinel) return;
    const s = tree.nodes.slice();
    collectPostOrder(tree, s.items(.left)[@intFromEnum(node)], out);
    collectPostOrder(tree, s.items(.right)[@intFromEnum(node)], out);
    out.appendAssumeCapacity(s.items(.key)[@intFromEnum(node)]);
}

test "iterator stress_iter_random" {
    const allocator = std.testing.allocator;
    var tree: RBTree(usize, usize, void, compare) = .init({});
    defer tree.deinit(allocator);

    var prng: std.Random.DefaultPrng = .init(0xcafebabedeadbeef);
    const rnd = prng.random();

    var remaining: std.AutoHashMap(usize, void) = .init(allocator);
    defer remaining.deinit();

    const ops = 10_000;
    for (0..ops) |_| {
        const key = rnd.int(usize);
        if (rnd.boolean()) {
            if (!remaining.contains(key)) {
                _ = try tree.insert(allocator, key, key);
                try remaining.put(key, {});
            }
        } else {
            if (remaining.remove(key)) {
                _ = try tree.delete(key);
            }
        }
    }

    var in_truth: std.ArrayList(usize) = try .initCapacity(allocator, remaining.count());
    var pre_truth: std.ArrayList(usize) = try .initCapacity(allocator, remaining.count());
    var post_truth: std.ArrayList(usize) = try .initCapacity(allocator, remaining.count());
    defer {
        in_truth.deinit();
        pre_truth.deinit();
        post_truth.deinit();
    }

    collectInOrder(&tree, tree.root, &in_truth);
    collectPreOrder(&tree, tree.root, &pre_truth);
    collectPostOrder(&tree, tree.root, &post_truth);

    var iter_in = try tree.inOrderIter(allocator);
    defer iter_in.deinit();
    var idx: usize = 0;
    while (try iter_in.next()) |n| : (idx += 1) {
        try std.testing.expectEqual(in_truth.items[idx], tree.nodes.items(.key)[@intFromEnum(n)]);
    }
    try std.testing.expect(idx == in_truth.items.len);

    var iter_pre = try tree.preOrderIter(allocator);
    defer iter_pre.deinit();
    idx = 0;
    while (try iter_pre.next()) |n| : (idx += 1) {
        try std.testing.expectEqual(pre_truth.items[idx], tree.nodes.items(.key)[@intFromEnum(n)]);
    }
    try std.testing.expect(idx == pre_truth.items.len);

    var iter_post = try tree.postOrderIter(allocator);
    defer iter_post.deinit();
    idx = 0;
    while (iter_post.next()) |n| : (idx += 1) {
        try std.testing.expectEqual(post_truth.items[idx], tree.nodes.items(.key)[@intFromEnum(n)]);
    }
    try std.testing.expect(idx == post_truth.items.len);
}

test "iterator stress_iter_pathological" {
    const allocator = std.testing.allocator;
    const n = 1_000;
    const rounds = 50;

    var tree: RBTree(usize, usize, void, compare) = .init({});
    defer tree.deinit(allocator);

    var buf: std.ArrayList(usize) = try .initCapacity(allocator, n);
    defer buf.deinit();

    for (0..rounds) |r| {
        for (0..n) |k| {
            _ = try tree.insert(allocator, k + r * n, 0);
        }
        buf.clearRetainingCapacity();
        collectInOrder(&tree, tree.root, &buf);
        try std.testing.expect(buf.items.len == n);
        var it = try tree.inOrderIter(allocator);
        defer it.deinit();
        var idx: usize = 0;
        while (try it.next()) |node| : (idx += 1) {
            try std.testing.expectEqual(buf.items[idx], tree.nodes.items(.key)[@intFromEnum(node)]);
        }
        try std.testing.expect(idx == buf.items.len);

        for (0..n) |k| {
            _ = try tree.delete(k + r * n);
        }
        try std.testing.expect(tree.root == .sentinel);

        for (0..n) |k| {
            const key = n - 1 - k + r * n;
            _ = try tree.insert(allocator, key, 0);
        }
        buf.clearRetainingCapacity();
        collectPreOrder(&tree, tree.root, &buf);
        var pre_it = try tree.preOrderIter(allocator);
        defer pre_it.deinit();
        idx = 0;
        while (try pre_it.next()) |node| : (idx += 1) {
            try std.testing.expectEqual(buf.items[idx], tree.nodes.items(.key)[@intFromEnum(node)]);
        }
        try std.testing.expect(idx == buf.items.len);

        for (0..n) |k| {
            _ = try tree.delete(k + r * n);
        }
        try std.testing.expect(tree.root == .sentinel);
    }
}

test "permutation insert order property" {
    const allocator = std.testing.allocator;
    var tree: RBTree(usize, void, void, compare) = .init({});
    defer tree.deinit(allocator);

    const n = 8;
    const perms = [_][n]usize{
        .{ 0, 1, 2, 3, 4, 5, 6, 7 },
        .{ 7, 6, 5, 4, 3, 2, 1, 0 },
        .{ 3, 1, 4, 0, 6, 2, 5, 7 },
        .{ 5, 2, 7, 1, 6, 0, 3, 4 },
    };

    for (perms) |perm| {
        for (perm) |k| {
            _ = try tree.insert(allocator, k, {});
        }
        var it = try tree.inOrderIter(allocator);
        defer it.deinit();
        var expect: usize = 0;
        while (try it.next()) |idx| : (expect += 1) {
            try std.testing.expectEqual(expect, tree.nodes.items(.key)[@intFromEnum(idx)]);
        }
        try std.testing.expect(expect == n);

        for (0..n) |k| {
            _ = try tree.delete(k);
        }
        try std.testing.expect(tree.root == .sentinel);
    }
}

test "ascending insert then descending delete" {
    const allocator = std.testing.allocator;
    var tree: RBTree(usize, usize, void, compare) = .init({});
    defer tree.deinit(allocator);

    const n = 256;
    for (0..n) |k| {
        _ = try tree.insert(allocator, k, 0);
    }

    try std.testing.expect(checkRBProperties(&tree));

    var k: usize = n;
    while (k > 0) : (k -= 1) {
        _ = try tree.delete(k - 1);
    }

    try std.testing.expect(tree.root == .sentinel);
    try std.testing.expect(tree.free_list != .sentinel);
}

test "find delete miss" {
    const allocator = std.testing.allocator;
    var tree: RBTree(usize, usize, void, compare) = .init({});
    defer tree.deinit(allocator);

    try std.testing.expect(tree.find(42) == null);
    try std.testing.expectEqual(null, try tree.delete(42));

    for (0..100) |k| {
        _ = try tree.insert(allocator, k, 0);
    }
    try std.testing.expect(tree.find(5000) == null);
    try std.testing.expectEqual(null, try tree.delete(5000));
}

test "node reuse for same key" {
    const allocator = std.testing.allocator;
    var tree: RBTree(usize, usize, void, compare) = .init({});
    defer tree.deinit(allocator);

    const key = 123;
    const rounds = 100;
    var first_idx: ?RBTree(usize, usize, void, compare).Node.Idx = null;

    for (0..rounds) |r| {
        _ = try tree.insert(allocator, key, r);
        const idx = tree.find(key).?;
        if (r == 0) {
            first_idx = idx;
        }
        _ = try tree.delete(key);
    }
    try std.testing.expect(first_idx.? == tree.free_list);
}
