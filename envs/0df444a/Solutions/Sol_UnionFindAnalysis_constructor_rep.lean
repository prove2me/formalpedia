-- Prove2me | solution 1 for UnionFindAnalysis.constructor_rep
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:54:57.971715+00:00
-- url     : https://prove2.me/submissions/2ae68acc-ffb3-47f6-b7d2-a76275cab3a4

import Definitions.Def_Algo_union_find_init_Analysis


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Union-find mathematics for implementations using union by rank.

The parent and rank maps describe the stored data. Representatives and masses
are proof-only witnesses: a root owns the mass of its component, and linking
two roots transfers all losing mass to the winner. Starting from singleton
components gives a fixed mass budget of `n`. A root of rank `r` owns at least
`2 ^ r` mass, so every find follows at most `log₂ n` parent links.

Path compression preserves these bounds and the represented partition. The
module proves a logarithmic worst-case bound, not an inverse-Ackermann amortized
bound. It imports no generated algorithm or execution model.
-/

namespace Algo2Lean.UnionFind









theorem total_ones (n : Nat) : total (n := n) (fun _ => 1) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [total, ih, Nat.add_comm]













theorem initial_valid (n : Nat) : Valid (initial n) := by
  constructor
  · intro vertex; rfl
  · intro vertex _; rfl
  · intro vertex; rfl
  · intro vertex different; exact False.elim (different rfl)
  · intro vertex _; simp [initial]
  · intro vertex different; exact False.elim (different rfl)
  · simp [initial, total_ones]





















































end Algo2Lean.UnionFind

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Construction of the reusable rank-and-compression disjoint-set structure.
The constructor allocates one object and two arrays, initializes singleton
components, and charges exactly `n + 1` initialization ticks. -/

namespace UnionFindAnalysis

open Algo2LeanCore Algo2LeanGenerated
open Algo.union_find Algo.union_find.Algo2LeanGenerated







































/-- Initializing parents preserves every other sequence. -/
theorem initializeEntries_other (heap : Heap) (parent other : SeqRef)
    (first : Int) (count : Nat) (different : other ≠ parent) :
    (initializeEntries heap parent first count).read other = heap.read other := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih =>
    rw [initializeEntries, ih]
    funext index
    simp [Heap.read, Heap.write, different]

/-- Writes in a later interval preserve all earlier entries. -/
theorem initializeEntries_before (heap : Heap) (parent : SeqRef)
    (first index : Int) (count : Nat) (earlier : index < first) :
    (initializeEntries heap parent first count).read parent index = heap.read parent index := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih =>
    rw [initializeEntries, ih _ _ (by omega)]
    simp [Heap.read, Heap.write, show index ≠ first by omega]

/-- Every initialized vertex becomes its own parent. -/
theorem initializeEntries_identity (heap : Heap) (parent : SeqRef)
    (first index : Int) (count : Nat) (lower : first ≤ index) (upper : index < first + count) :
    (initializeEntries heap parent first count).read parent index = index := by
  induction count generalizing heap first with
  | zero => omega
  | succ count ih =>
    rw [initializeEntries]
    by_cases same : index = first
    · rw [initializeEntries_before _ _ _ _ _ (by omega)]
      simp [same]
    · exact ih _ _ (by omega) (by omega)







/-- Construction establishes the singleton partition and all rank invariants. -/
theorem constructor_rep (heap : Heap) (size : Nat) :
    Rep (newHeap heap size) (newLayout heap) (Algo2Lean.UnionFind.initial size) := by
  have allocated : is_UnionFind (heap.allocateObject "union_find.UnionFind") heap.nextObject := by
    simp [is_UnionFind]
  refine ⟨Algo2Lean.UnionFind.initial_valid size, initializedHeap_valid _ _ _ allocated,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [newHeap, newLayout, initializedHeap, field_UnionFind_parent, is_UnionFind] using!
      prepareInitialHeap_parent _ _ (size : Int) allocated
  · simpa [newHeap, newLayout, initializedHeap, field_UnionFind_rank, is_UnionFind] using!
      prepareInitialHeap_rank _ _ (size : Int) allocated
  · simpa [newHeap, newLayout, initializedHeap, field_UnionFind_size, is_UnionFind] using!
      prepareInitialHeap_size _ _ (size : Int) allocated
  · simp [newHeap, newLayout, initializedHeap]
  · simp [newHeap, newLayout, initializedHeap]
  · simp [newLayout]
  · intro vertex
    exact initializeEntries_identity _ _ 0 vertex.val size (Int.natCast_nonneg _) (by have := vertex.isLt; omega)
  · intro vertex
    have other := initializeEntries_other
      ((prepareInitialHeap (heap.allocateObject "union_find.UnionFind") heap.nextObject size).tick "uf_init")
      heap.nextRef (heap.nextRef + 1) 0 size (Nat.ne_of_gt (Nat.lt_succ_self _))
    change (initializeEntries _ heap.nextRef 0 size).read (heap.nextRef + 1) vertex.val = 0
    rw [other]
    simp [prepareInitialHeap, set_UnionFind_size, set_UnionFind_rank, set_UnionFind_parent,
      Heap.read, Heap.allocate]







-- Main result: Correctness and running time













end UnionFindAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ (heap : Algo2LeanGenerated.Heap) (size : Nat),
      UnionFindAnalysis.Rep (UnionFindAnalysis.newHeap heap size) (UnionFindAnalysis.newLayout heap)
        (Algo2Lean.UnionFind.initial size) :=
  UnionFindAnalysis.constructor_rep
