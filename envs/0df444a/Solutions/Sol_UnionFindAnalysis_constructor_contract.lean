-- Prove2me | solution 1 for UnionFindAnalysis.constructor_contract
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:56:35.859551+00:00
-- url     : https://prove2.me/submissions/95c803cd-3e99-4c0d-bd00-905ed4d0c1f9

import Definitions.Def_Algo_union_find_init_Analysis
import Theorems.Thm_UnionFindAnalysis_constructor_summary
import Theorems.Thm_UnionFindAnalysis_constructor_rep


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





/-- Each initialized entry contributes one tick and changes no other clock. -/
theorem initializeEntries_clocks (heap : Heap) (parent : SeqRef)
    (first : Int) (count : Nat) (clock : String) :
    (initializeEntries heap parent first count).clocks clock =
      heap.clocks clock + if clock = "uf_init" then count else 0 := by
  induction count generalizing heap first with
  | zero => simp [initializeEntries]
  | succ count ih =>
    rw [initializeEntries, ih]
    by_cases same : clock = "uf_init" <;> simp [Heap.tick, same, Nat.add_assoc, Nat.add_comm]







/-- The constructor charges exactly one initial tick plus one per vertex. -/
theorem constructor_clocks (heap : Heap) (size : Nat) (clock : String) :
    (newHeap heap size).clocks clock = heap.clocks clock +
      if clock = "uf_init" then size + 1 else 0 := by
  simp only [newHeap, initializedHeap, initializeEntries_clocks]
  by_cases same : clock = "uf_init" <;>
    simp [prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank, set_UnionFind_size,
      Heap.tick, same, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Constructor allocation adds exactly two integer sequences and one object,
    and leaves the collection allocation boundary unchanged. -/
theorem constructor_allocations (heap : Heap) (size : Nat) :
    (newHeap heap size).nextRef = heap.nextRef + 2 ∧
    (newHeap heap size).nextObject = heap.nextObject + 1 ∧
    (newHeap heap size).nextCollection = heap.nextCollection := by
  simp [newHeap, initializedHeap, prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank,
    set_UnionFind_size, Nat.add_assoc]

/-- All old storage survives construction; the new arrays and object are fresh. -/
theorem constructor_frame (heap : Heap) (size : Nat) :
    (∀ ref, ref < heap.nextObject → (newHeap heap size).objects ref = heap.objects ref) ∧
    (∀ ref, ref < heap.nextRef → (newHeap heap size).read ref = heap.read ref) ∧
    (newHeap heap size).collections = heap.collections := by
  refine ⟨?_, ?_, ?_⟩
  · intro ref old
    simp [newHeap, initializedHeap, prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank,
      set_UnionFind_size, Heap.writeField, Heap.allocateObject, Nat.ne_of_lt old]
  · intro ref old
    have different : ref ≠ heap.nextRef := Nat.ne_of_lt old
    simp only [newHeap, initializedHeap, Heap.allocateObject_nextRef,
      initializeEntries_other _ _ _ _ _ different]
    funext index
    simp [prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank, set_UnionFind_size,
      Heap.read, Heap.allocate, different, show ref ≠ heap.nextRef + 1 by omega]
  · simp [newHeap, initializedHeap, prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank,
      set_UnionFind_size]

-- Main result: Correctness and running time





/-- Initialization has exact increments for arbitrary initial caller counters. -/
theorem constructor_increments (heap : Heap) (size : Nat) :
    heap.Increments (newHeap heap size) (constructorCosts size) :=
  constructor_clocks heap size

/-- All existing storage is framed out of construction. Its object and arrays
    are fresh allocations, so its modification footprint is empty. -/
theorem constructor_footprint (heap : Heap) (size : Nat) :
    heap.Footprint (newHeap heap size) [] [] [] := by
  obtain ⟨objects, sequences, collections⟩ := constructor_frame heap size
  obtain ⟨nextRef, nextObject, nextCollection⟩ := constructor_allocations heap size
  refine ⟨by rw [nextRef]; omega, by rw [nextObject]; omega, by simp only [nextCollection, Nat.le_refl],
    ?_, ?_, ?_, ?_, ?_⟩
  · intro ref old
    simp only [Heap.objectClass, objects ref old]
  · intro ref old
    simp only [Heap.sequenceType, collections]
  · intro ref old _
    exact sequences ref old
  · intro ref old _
    exact objects ref old
  · intro ref old _
    rw [collections]

/-- Construction is reusable beneath an arbitrary caller: it establishes the
    initial mathematical partition, preserves all old storage, records exact
    clock increments, and allocates exactly two sequences and one object. -/
theorem constructor_contract (heap : Heap) (size : Nat) :
    UnionFind.Call heap (size : Int) (newHeap heap size) heap.nextObject ∧
    Rep (newHeap heap size) (newLayout heap) (Algo2Lean.UnionFind.initial size) ∧
    heap.Footprint (newHeap heap size) [] [] [] ∧
    heap.Increments (newHeap heap size) (constructorCosts size) ∧
    (newHeap heap size).nextRef = heap.nextRef + 2 ∧
    (newHeap heap size).nextObject = heap.nextObject + 1 ∧
    (newHeap heap size).nextCollection = heap.nextCollection :=
  ⟨constructor_summary heap size, constructor_rep heap size, constructor_footprint heap size,
    constructor_increments heap size, constructor_allocations heap size⟩



end UnionFindAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ (heap : Algo2LeanGenerated.Heap) (size : Nat),
      Algo.union_find.UnionFind.Call heap (↑size : Int) (UnionFindAnalysis.newHeap heap size)
          heap.nextObject ∧
        UnionFindAnalysis.Rep (UnionFindAnalysis.newHeap heap size) (UnionFindAnalysis.newLayout heap)
            (Algo2Lean.UnionFind.initial size) ∧
          heap.Footprint (UnionFindAnalysis.newHeap heap size) List.nil.{0} List.nil.{0} List.nil.{0} ∧
            heap.Increments (UnionFindAnalysis.newHeap heap size)
                (UnionFindAnalysis.constructorCosts size) ∧
              Eq.{1} (UnionFindAnalysis.newHeap heap size).nextRef
                  (HAdd.hAdd.{0, 0, 0} heap.nextRef (2 : Nat)) ∧
                Eq.{1} (UnionFindAnalysis.newHeap heap size).nextObject
                    (HAdd.hAdd.{0, 0, 0} heap.nextObject (1 : Nat)) ∧
                  Eq.{1} (UnionFindAnalysis.newHeap heap size).nextCollection heap.nextCollection :=
  UnionFindAnalysis.constructor_contract
