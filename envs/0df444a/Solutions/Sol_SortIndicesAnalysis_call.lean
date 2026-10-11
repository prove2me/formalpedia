-- Prove2me | solution 1 for SortIndicesAnalysis.call
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:56:34.731675+00:00
-- url     : https://prove2.me/submissions/54b6506a-e155-4458-9588-182942a6c718

import Definitions.Def_Algo_sort_indices_Analysis
import Theorems.Thm_BinaryModuleAnalysis_insert_correct
import Theorems.Thm_BinaryModuleAnalysis_pop_singleton_correct
import Theorems.Thm_BinaryModuleAnalysis_pop_multiple_correct


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Analysis outline:
- `new_heap_rep`: Empty heap representation.
- `insert_correct`: Insertion correctness and cost.
- `decrease_correct`: Decrease-key correctness and cost.
- `pop_correct`: Minimum extraction correctness and cost.
-/

open Algo.indexed_heap Algo.indexed_heap.Algo2LeanGenerated

open Algo2LeanCore Algo2LeanGenerated

namespace BinaryModuleAnalysis

-- A small source-facing description of the object's storage. The three arrays
-- are separate mutable sequences; aliases to the MinHeap object remain valid.




-- These observations use only the generated field interface. Updating an
-- array does not replace the object's fields or change its identity.




-- Exact heap effect of swap, including the cost counter. The original two
-- vertices are read before either array is changed, including when i = j.




-- A permutation of positions, with all other positions left fixed.










-- No duplicate active vertices, no stale positive positions, and exactly -1
-- for vertices outside the heap. These are finite-prefix map invariants.








-- Swapping two valid heap positions preserves the inverse map, including a
-- self-swap. No heap-order assumption or concrete input values are required.


-- Position numbers may change, but exactly the same vertices remain present.






-- Simple endpoint cases are checked against the compiled methods as well.






-- The mathematical depth is the prospective logarithmic bound. Each upward
-- move decreases it by exactly one; downward moves increase it by one.








-- Construction keeps its heap effect in source order. Each sequence has a
-- distinct fresh reference, and the empty queue has no present vertices.




theorem initialized_object (heap : Heap) (queue : Ref_MinHeap)
    (valid : is_MinHeap heap queue) : is_MinHeap (initializedHeap heap queue) queue := by
  simpa [initializedHeap, is_MinHeap, set_MinHeap_vertices, set_MinHeap_positions,
    set_MinHeap_keys, set_MinHeap_size] using valid

theorem initialization_summary (heap : Heap) (queue : Ref_MinHeap)
    (valid : is_MinHeap heap queue) :
    MinHeap.__init__.Call heap queue (initializedHeap heap queue) () := by
  refine ⟨valid, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap___init___pc15 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc14 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc13 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc12 _ _ _
    (by simpa [is_MinHeap] using valid))
  apply Reaches.prepend (Step.MinHeap___init___pc11 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc10 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc9 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc8 _ _ _
    (by simpa [is_MinHeap, set_MinHeap_vertices] using valid))
  apply Reaches.prepend (Step.MinHeap___init___pc7 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc6 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc5 _ _ _)
  apply Reaches.prepend (Step.MinHeap___init___pc4 _ _ _
    (by simpa [is_MinHeap, set_MinHeap_vertices, set_MinHeap_positions] using valid))
  apply Reaches.prepend (Step.MinHeap___init___pc3 _ _ _
    (by simpa [is_MinHeap, set_MinHeap_vertices, set_MinHeap_positions,
      set_MinHeap_keys] using valid))
  apply Reaches.prepend (Step.MinHeap___init___pc2 _ _ _)
  exact Reaches.single (Step.MinHeap___init___pc1 _ _ _)



theorem new_heap_summary (heap : Heap) :
    MinHeap.Call heap () (newHeap heap) heap.nextObject := by
  have allocated : is_MinHeap (heap.allocateObject "indexed_heap.MinHeap") heap.nextObject := by
    simp [is_MinHeap]
  refine ⟨True.intro, ?_⟩
  intro stack
  apply Reaches.prepend (Step.MinHeap_pc6 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pc5 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pc4 _ _ _)
  apply Reaches.prepend (Step.MinHeap_pc3 _ _ _)
  apply Reaches.trans ((initialization_summary _ _ allocated).2 _)
  apply Reaches.prepend (Step.MinHeap_pc2 _ _ _)
  exact Reaches.single (Step.MinHeap_pc1 _ _ _ (initialized_object _ _ allocated))

theorem initialization_layout (heap : Heap) (queue : Ref_MinHeap)
    (valid : is_MinHeap heap queue) :
    (emptyLayout heap).Valid (initializedHeap heap queue) queue := by
  have object := initialized_object heap queue valid
  have present := valid.2
  constructor
  · exact object
  · simp [emptyLayout, initializedHeap, field_MinHeap_vertices, set_MinHeap_vertices,
      set_MinHeap_positions, set_MinHeap_keys, set_MinHeap_size, is_MinHeap,
      valid.1, present, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_MinHeap_positions, set_MinHeap_vertices,
      set_MinHeap_positions, set_MinHeap_keys, set_MinHeap_size, is_MinHeap,
      valid.1, present, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_MinHeap_keys, set_MinHeap_vertices,
      set_MinHeap_positions, set_MinHeap_keys, set_MinHeap_size, is_MinHeap,
      valid.1, present, ObjectValue.asSeq, Nat.add_assoc]
  · simp [emptyLayout, initializedHeap, field_MinHeap_size, set_MinHeap_vertices,
      set_MinHeap_positions, set_MinHeap_keys, set_MinHeap_size, is_MinHeap,
      valid.1, present, ObjectValue.asInt, Nat.add_assoc]
  · change heap.nextRef < heap.nextRef + 3
    omega
  · change heap.nextRef + 1 < heap.nextRef + 3
    omega
  · change heap.nextRef + 2 < heap.nextRef + 3
    omega
  · change heap.nextRef ≠ heap.nextRef + 1
    omega
  · change heap.nextRef ≠ heap.nextRef + 2
    omega
  · change heap.nextRef + 1 ≠ heap.nextRef + 2
    omega

theorem initialized_positions (heap : Heap) (queue : Ref_MinHeap) (vertex : Int) :
    (initializedHeap heap queue).read (emptyLayout heap).positions vertex = -1 := by
  simp [initializedHeap, emptyLayout, Heap.read, Heap.allocate, set_MinHeap_vertices,
    set_MinHeap_positions, set_MinHeap_keys, set_MinHeap_size]

theorem new_heap_layout (heap : Heap) :
    (emptyLayout heap).Valid (newHeap heap) heap.nextObject := by
  exact initialization_layout (heap.allocateObject "indexed_heap.MinHeap") heap.nextObject (by simp [is_MinHeap])

theorem new_heap_positions (heap : Heap) (vertex : Int) :
    (newHeap heap).read (emptyLayout heap).positions vertex = -1 := by
  exact initialized_positions (heap.allocateObject "indexed_heap.MinHeap") heap.nextObject vertex

theorem new_heap_clocks (heap : Heap) : (newHeap heap).clocks = heap.clocks := rfl

































-- Client-owned arrays, such as Dijkstra's distances and settled flags, are
-- unchanged by creating and manipulating this separate priority queue.
theorem new_heap_read_old (heap : Heap) (ref : SeqRef) (index : Int)
    (allocated : ref < heap.nextRef) :
    (newHeap heap).read ref index = heap.read ref index := by
  have first : ref ≠ heap.nextRef := Nat.ne_of_lt allocated
  have second : ref ≠ heap.nextRef + 1 :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le allocated (Nat.le_add_right _ _))
  have third : ref ≠ heap.nextRef + 2 :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le allocated (Nat.le_add_right _ _))
  simp [newHeap, initializedHeap, set_MinHeap_vertices, set_MinHeap_positions,
    set_MinHeap_keys, set_MinHeap_size, Heap.read, Heap.allocate, Heap.allocateObject,
    first, second, third, Nat.add_assoc]



























-- The loop proof is expressed through the named source location and its two
-- live inputs. Other temporary locals are irrelevant to the specification.










theorem Layout.Valid.tick {layout : Layout} {heap : Heap} {queue : Ref_MinHeap}
    (valid : layout.Valid heap queue) (name : String) (amount : Nat := 1) :
    layout.Valid (heap.tick name amount) queue := by
  exact ⟨valid.object, valid.readVertices, valid.readPositions, valid.readKeys,
    valid.readSize, valid.verticesAllocated, valid.positionsAllocated, valid.keysAllocated,
    valid.verticesPositions, valid.verticesKeys, valid.positionsKeys⟩







-- One unsuccessful comparison swaps with the parent and returns to the named
-- loop location. Any proof for the remaining loop can be plugged in here.


-- Reordering the integer arrays leaves object fields, typed collections, and
-- all allocation counters unchanged. In particular, graph objects in a caller
-- remain available with their original fields after either sifting method.






-- The remaining loop has one final heap for every configuration with these
-- source inputs. Induction follows tree depth, not the transcript length.


-- A valid active index always terminates. The map invariant is preserved, and
-- each of the two instrumented operation counts is at most floor(log2(i+1)).
-- Sift-up repairs its expected single-edge order exception. Keys and client
-- arrays are preserved because only the vertices and positions arrays change.












/-- Array writes preserve the object's fields, reference bounds, and separation. -/
theorem Layout.Valid.write {heap : Heap} {queue : Ref_MinHeap} {layout : Layout}
    (valid : layout.Valid heap queue) (ref : SeqRef) (index value : Int) :
    layout.Valid (heap.write ref index value) queue := by
  exact ⟨valid.object, valid.readVertices, valid.readPositions, valid.readKeys,
    valid.readSize, valid.verticesAllocated, valid.positionsAllocated, valid.keysAllocated,
    valid.verticesPositions, valid.verticesKeys, valid.positionsKeys⟩























/-- Every constructor call supplies a valid empty priority queue. -/
theorem new_heap_rep (heap : Heap) :
    QueueRep (newHeap heap) heap.nextObject (emptyLayout heap) := by
  refine ⟨new_heap_layout heap, by simp [emptyLayout], ?_, ?_⟩
  · constructor
    · intro index lower upper
      change index < 0 at upper
      omega
    · intro vertex present
      rw [new_heap_positions] at present
      omega
    · intro vertex _
      exact new_heap_positions heap vertex
  · intro child positive upper
    change child < 0 at upper
    omega



















-- Sift-down first selects the smaller child, then compares it with the parent.




















theorem depth_mono {first second : Int} (ordered : first ≤ second) : depth first ≤ depth second := by
  unfold depth
  apply (Nat.le_log2 (by omega)).2
  exact Nat.le_trans (Nat.log2_self_le (by omega)) (by omega)





-- Induction descends through the tree. Each non-leaf iteration examines at
-- most two keys and exchanges at most one pair of heap positions.


-- The public contract allows arbitrary initial priorities. Its conditional
-- repair clause explains when this terminating run also restores heap order.








































/-- Every nonempty represented queue has a terminating minimum extraction with
    logarithmic operation costs and a reusable heap-level postcondition. -/
theorem pop_correct (heap : Heap) (queue : Ref_MinHeap) (layout : Layout)
    (representation : QueueRep heap queue layout) (nonempty : 0 < layout.size) :
    ∃ after, MinHeap.pop_min.Call heap queue after (heap.read layout.vertices 0) ∧
      Extracted heap after queue layout (heap.read layout.vertices 0) := by
  by_cases multiple : 1 < layout.size
  · exact pop_multiple_correct heap queue layout representation multiple
  · exact pop_singleton_correct heap queue layout representation (by omega)





end BinaryModuleAnalysis

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Sorting identifiers keeps weights in their original sequence. The insertion
phase reuses the proved heap insertion contract; the extraction phase reuses
minimum extraction. Neither phase unfolds a heap operation's transitions.
-/

open Algo2LeanCore Algo2LeanGenerated
open Algo.indexed_heap.Algo2LeanGenerated hiding Step Frame Result Configuration Stack Transcript
open Algo.sort_indices Algo.sort_indices.Algo2LeanGenerated
open BinaryModuleAnalysis

namespace SortIndicesAnalysis









private theorem Budget.refl (count : Int) (heap : Heap) : Budget count 0 heap heap := by
  intro clock
  simp

private theorem Budget.trans {count : Int} {first second : Nat} {a b c : Heap}
    (one : Budget count first a b) (two : Budget count second b c) :
    Budget count (first + second) a c := by
  intro clock
  have := one clock
  have := two clock
  simp only [Nat.add_mul]
  omega



private theorem Storage.refl (queue : ObjectRef) (refs : List SeqRef) (heap : Heap) :
    Storage queue refs heap heap := ⟨by intros; rfl, by intros; rfl, rfl, rfl, rfl, rfl, by intros; rfl⟩

private theorem Storage.trans {queue : ObjectRef} {refs : List SeqRef} {a b c : Heap}
    (one : Storage queue refs a b) (two : Storage queue refs b c) : Storage queue refs a c :=
  ⟨fun ref outside => (two.arrays ref outside).trans (one.arrays ref outside),
   fun ref outside => (two.objects ref outside).trans (one.objects ref outside),
   two.nextRef.trans one.nextRef, two.nextObject.trans one.nextObject,
   two.collections.trans one.collections, two.nextCollection.trans one.nextCollection,
   fun name source comparisons swaps =>
     (two.clocks name source comparisons swaps).trans (one.clocks name source comparisons swaps)⟩

private theorem Storage.tick (queue : ObjectRef) (refs : List SeqRef) (heap : Heap) :
    Storage queue refs heap (heap.tick "sort_steps") :=
  ⟨by intros; rfl, by intros; rfl, rfl, rfl, rfl, rfl,
    by intro name source _ _; simp [Heap.tick, source]⟩

private theorem Storage.write (queue : ObjectRef) (refs : List SeqRef) (heap : Heap)
    (result : SeqRef) (member : result ∈ refs) (index value : Int) :
    Storage queue refs heap (heap.write result index value) := by
  refine ⟨?_, by intros; rfl, rfl, rfl, rfl, rfl, by intros; rfl⟩
  intro ref outside
  have different : ref ≠ result := by intro same; subst ref; exact outside member
  funext index
  simp [Heap.read, Heap.write, different]

private theorem Storage.of_heap {before after : Heap} {queue : ObjectRef}
    {layout : Layout} {result : SeqRef} {size : Int}
    (arrays : ∀ ref, ref ≠ layout.vertices → ref ≠ layout.positions → ref ≠ layout.keys →
      ∀ index, after.read ref index = before.read ref index)
    (storage : OtherStoragePreserved (set_MinHeap_size before queue size) after)
    (clocks : ∀ name, name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
      after.clocks name = before.clocks name) :
    Storage queue [layout.vertices, layout.positions, layout.keys, result] before after := by
  refine ⟨?_, ?_, storage.nextRef, storage.nextObject, storage.collections, storage.nextCollection,
    fun name _ comparisons swaps => clocks name comparisons swaps⟩
  · intro ref outside
    simp only [List.mem_cons, not_or] at outside
    funext index
    exact arrays ref outside.1 outside.2.1 outside.2.2.1 index
  · intro ref outside
    rw [storage.objects]
    simp [set_MinHeap_size, Heap.writeField, outside]

private theorem queue_tick {heap : Heap} {queue : ObjectRef} {layout : Layout}
    (represented : QueueRep heap queue layout) :
    QueueRep (heap.tick "sort_steps") queue layout :=
  ⟨represented.valid.tick "sort_steps", represented.nonnegative, represented.indexed, represented.ordered⟩

private theorem queue_write {heap : Heap} {queue : ObjectRef} {layout : Layout}
    (represented : QueueRep heap queue layout) (ref : SeqRef) (index value : Int)
    (separate : ref ≠ layout.vertices ∧ ref ≠ layout.positions ∧ ref ≠ layout.keys) :
    QueueRep (heap.write ref index value) queue layout := by
  refine ⟨represented.valid.write ref index value, represented.nonnegative, ?_, ?_⟩
  · have vertices : (heap.write ref index value).read layout.vertices = heap.read layout.vertices := by
      funext position; simp [Heap.read, Heap.write, Ne.symm separate.1]
    have positions : (heap.write ref index value).read layout.positions = heap.read layout.positions := by
      funext position; simp [Heap.read, Heap.write, Ne.symm separate.2.1]
    rw [vertices, positions]
    exact represented.indexed
  · simpa [Heap.read, Heap.write, Ne.symm separate.1, Ne.symm separate.2.2] using represented.ordered

private theorem operation_budget {before after : Heap} {count size : Int}
    (within : size ≤ count)
    (comparisons : Heap.cost (before.tick "sort_steps") after "heap_comparisons" ≤ 2 * depth size)
    (swaps : Heap.cost (before.tick "sort_steps") after "heap_swaps" ≤ depth size + 1)
    (other : ∀ name, name ≠ "heap_comparisons" → name ≠ "heap_swaps" →
      after.clocks name = (before.tick "sort_steps").clocks name) : Budget count 1 before after := by
  have depthBound := depth_mono within
  intro clock
  by_cases comparison : clock = "heap_comparisons"
  · subst clock
    simp only [Heap.cost, Heap.tick, String.reduceEq, ↓reduceIte] at comparisons
    simp only [rate, String.reduceEq, ↓reduceIte, Nat.one_mul]
    omega
  by_cases swap : clock = "heap_swaps"
  · subst clock
    simp only [Heap.cost, Heap.tick, String.reduceEq, ↓reduceIte] at swaps
    simp only [rate, String.reduceEq, ↓reduceIte, Nat.one_mul]
    omega
  rw [other clock comparison swap]
  by_cases source : clock = "sort_steps"
  · subst clock; simp [rate, Heap.tick]
  · simp [rate, Heap.tick, source, comparison, swap]





/-- One source loop iteration uses the existing minimum-extraction theorem. -/
private theorem extract_continue (heap after final : Heap) (state : State_sort_indices)
    (vertex : Int) (running : state.v4 < state.v1)
    (allocated : state.v3 < after.nextRef)
    (call : Algo.indexed_heap.MinHeap.pop_min.Call (heap.tick "sort_steps") state.v2 after vertex)
    (rest : Summary Step (after.write state.v3 state.v4 vertex)
      (.fn_sort_indices 4 (afterExtract state vertex)) final (.fn_sort_indices state.v3)) :
    Summary Step heap (.fn_sort_indices 4 state) final (.fn_sort_indices state.v3) := by
  intro caller
  apply Reaches.prepend (Step.sort_indices_pc4 _ _ _)
  apply Reaches.prepend (Step.sort_indices_pc3_true _ _ _ (by simpa using running))
  apply Reaches.prepend (Step.sort_indices_pc12 _ _ _)
  apply Reaches.prepend (Step.sort_indices_pc11 _ _ _)
  apply Reaches.prepend (Step.sort_indices_pc10 _ _ _ (by exact call.1))
  apply Reaches.prepend (Step.sort_indices_pc9 _ _ _)
  apply (ModuleCall.summary import_0_simulates _ caller call.2).trans
  apply Reaches.prepend (Step.sort_indices_pc8 _ _ _)
  apply Reaches.prepend (Step.sort_indices_pc7 _ _ _)
  apply Reaches.prepend (Step.sort_indices_pc6 _ _ _ allocated)
  apply Reaches.prepend (Step.sort_indices_pc5 _ _ _)
  simpa [afterExtract, running] using rest caller

/-- Repeated minimum extraction produces a sorted permutation of precisely the
    remaining identifiers and never rewrites the completed output prefix. -/
private theorem extract_loop (count : Int) (fuel : Nat) (keys : Seq) :
    ∀ (heap : Heap) (state : State_sort_indices) (layout : Layout) (remaining : List Int),
    remaining.length = fuel → remaining.Nodup → state.v1 = count →
    0 ≤ state.v4 → state.v4 + (fuel : Int) = count →
    layout.size = (fuel : Int) → QueueRep heap state.v2 layout →
    Contents keys remaining heap layout → state.v3 < heap.nextRef →
    state.v3 ≠ layout.vertices ∧ state.v3 ≠ layout.positions ∧ state.v3 ≠ layout.keys →
    ∃ (final : Heap) (values : List Int),
      Summary Step heap (.fn_sort_indices 4 state) final (.fn_sort_indices state.v3) ∧
      values.Perm remaining ∧ values.Pairwise (fun a b => keys a ≤ keys b) ∧
      (∀ index : Nat, index < values.length →
        final.read state.v3 (state.v4 + index) = values[index]!) ∧
      (∀ index : Int, index < state.v4 → final.read state.v3 index = heap.read state.v3 index) ∧
      Storage state.v2 [layout.vertices, layout.positions, layout.keys, state.v3] heap final ∧
      Budget count fuel heap final := by
  induction fuel with
  | zero =>
    intro heap state layout remaining length unique total index finish size represented contents allocated separate
    have empty : remaining = [] := List.eq_nil_of_length_eq_zero length
    subst remaining
    refine ⟨heap, [], ?_, List.Perm.refl _, by simp, by simp, by intros; rfl,
      Storage.refl _ _ _, Budget.refl _ _⟩
    intro caller
    apply Reaches.prepend (Step.sort_indices_pc4 _ _ _)
    apply Reaches.prepend (Step.sort_indices_pc3_false _ _ _ (by simp; omega))
    apply Reaches.prepend (Step.sort_indices_pc2 _ _ _)
    exact Reaches.single (Step.sort_indices_pc1 _ _ _ allocated)
  | succ fuel ih =>
    intro heap state layout remaining length unique total index finish size represented contents allocated separate
    obtain ⟨after, call, effect⟩ := pop_correct (heap.tick "sort_steps") state.v2 layout
      (queue_tick represented) (by omega)
    let vertex := heap.read layout.vertices 0
    have member : vertex ∈ remaining := (contents.1 vertex).mp effect.wasPresent
    have erasedLength : (remaining.erase vertex).length = fuel := by
      have := Algo2Lean.FiniteIndex.erase_length remaining vertex member
      omega
    let written := after.write state.v3 state.v4 vertex
    let next := afterExtract state vertex
    let shorter := { layout with size := layout.size - 1 }
    have nextContents : Contents keys (remaining.erase vertex) written shorter := by
      constructor
      · intro value
        simp only [written, shorter, Heap.read, Heap.write,
          Ne.symm separate.2.1, false_and, ↓reduceIte]
        change 0 ≤ after.read layout.positions value ↔ _
        rw [effect.membership value]
        change (0 ≤ heap.read layout.positions value ∧ value ≠ vertex) ↔ _
        rw [contents.1 value, unique.mem_erase_iff]
        exact and_comm
      · intro value present
        have oldMember := List.mem_of_mem_erase present
        have keyEq := effect.keys value
        change written.read layout.keys value = keys value
        have all := keyEq.trans (contents.2 value oldMember)
        simpa [written, Heap.read, Heap.write, Ne.symm separate.2.2] using all
    obtain ⟨final, values, rest, permutation, sorted, output, kept, storage, budget⟩ :=
      ih written next shorter (remaining.erase vertex) erasedLength (unique.erase vertex) total
        (by dsimp [next, afterExtract]; omega) (by dsimp [next, afterExtract]; omega)
        (by dsimp [shorter]; omega) (queue_write effect.representation _ _ _ separate)
        nextContents (by dsimp [written]; rw [effect.otherStorage.nextRef]; exact allocated) separate
    have valuesLength : values.length = fuel := permutation.length_eq.trans erasedLength
    have popStorage := Storage.of_heap (result := state.v3)
      (fun ref vertices positions _ position => effect.otherArrays ref vertices positions position)
      effect.otherStorage effect.otherClocks
    have iterationStorage : Storage state.v2
        [layout.vertices, layout.positions, layout.keys, state.v3] heap written :=
      ((Storage.tick _ _ _).trans popStorage).trans (Storage.write _ _ _ _ (by simp) _ _)
    have iterationBudget : Budget count 1 heap written :=
      operation_budget (by omega : layout.size - 2 ≤ count) effect.comparisons effect.swaps effect.otherClocks
    refine ⟨final, vertex :: values,
      extract_continue heap after final state vertex (by omega)
        (by rw [effect.otherStorage.nextRef]; exact allocated) call rest,
      (permutation.cons vertex).trans (List.perm_cons_erase member).symm, ?_, ?_, ?_,
      iterationStorage.trans storage, ?_⟩
    · apply List.pairwise_cons.mpr
      refine ⟨?_, sorted⟩
      intro value present
      have oldMember := List.mem_of_mem_erase (permutation.mem_iff.mp present)
      have minimum := effect.minimum value ((contents.1 value).mpr oldMember)
      change heap.read layout.keys vertex ≤ heap.read layout.keys value at minimum
      simpa only [contents.2 vertex member, contents.2 value oldMember] using minimum
    · intro position within
      cases position with
      | zero =>
        have keep := kept state.v4 (by dsimp [next, afterExtract]; omega)
        simpa [next, afterExtract, written, Heap.read, Heap.write] using keep
      | succ position =>
        have keep := output position (by simp only [List.length_cons] at within; omega)
        simpa [next, afterExtract, Int.natCast_add, Int.add_assoc, Int.add_left_comm,
          Int.add_comm] using keep
    · intro position before
      have keep := kept position (by dsimp [next, afterExtract]; omega)
      have unchanged := effect.otherArrays state.v3 separate.1 separate.2.1 position
      have writtenRead : written.read state.v3 position = heap.read state.v3 position := by
        simpa [written, Heap.read, Heap.write, show position ≠ state.v4 by omega] using unchanged
      exact keep.trans writtenRead
    · have all := iterationBudget.trans budget
      simpa [Nat.add_comm] using all



/-- One insertion iteration reads an unchanged input key and applies the
    independently proved heap insertion contract. -/
private theorem insert_continue (heap after final : Heap) (state : State_sort_indices)
    (running : state.v4 < state.v1) (allocated : state.v0 < heap.nextRef)
    (call : Algo.indexed_heap.MinHeap.push_or_decrease.Call (heap.tick "sort_steps")
      (state.v2, state.v4, heap.read state.v0 state.v4) after ())
    (rest : Summary Step after
      (.fn_sort_indices 15 (afterInsert state (heap.read state.v0 state.v4))) final (.fn_sort_indices state.v3)) :
    Summary Step heap (.fn_sort_indices 15 state) final (.fn_sort_indices state.v3) := by
  intro caller
  apply Reaches.prepend (Step.sort_indices_pc15 _ _ _)
  apply Reaches.prepend (Step.sort_indices_pc14_true _ _ _ (by simpa using running))
  apply Reaches.prepend (Step.sort_indices_pc22 _ _ _)
  apply Reaches.prepend (Step.sort_indices_pc21 _ _ _)
  apply Reaches.prepend (Step.sort_indices_pc20 _ _ _ (by exact call.1))
  apply Reaches.prepend (Step.sort_indices_pc19 _ _ _)
  apply Reaches.prepend (Step.sort_indices_pc18 _ _ _ (by exact allocated))
  apply Reaches.prepend (Step.sort_indices_pc17 _ _ _)
  apply (ModuleCall.summary import_0_simulates _ caller call.2).trans
  apply Reaches.prepend (Step.sort_indices_pc16 _ _ _)
  simpa [afterInsert, running] using rest caller

/-- The insertion invariant records exactly the identifiers already inserted;
    all input weights retain their original values. -/
private theorem insert_loop (count : Int) (fuel : Nat) (keys : Seq) :
    ∀ (heap : Heap) (state : State_sort_indices) (layout : Layout),
    state.v1 = count → 0 ≤ state.v4 → state.v4 + (fuel : Int) = count →
    layout.size = state.v4 → QueueRep heap state.v2 layout →
    Contents keys (Algo2Lean.FiniteIndex.range state.v4) heap layout →
    heap.read state.v0 = keys → state.v0 < heap.nextRef → state.v3 < heap.nextRef →
    state.v0 ≠ layout.vertices ∧ state.v0 ≠ layout.positions ∧ state.v0 ≠ layout.keys →
    state.v3 ≠ layout.vertices ∧ state.v3 ≠ layout.positions ∧ state.v3 ≠ layout.keys →
    ∃ (final : Heap),
      Summary Step heap (.fn_sort_indices 15 state) final (.fn_sort_indices state.v3) ∧
      SortedPermutation keys count (final.read state.v3) ∧
      Storage state.v2 [layout.vertices, layout.positions, layout.keys, state.v3] heap final ∧
      Budget count (fuel + count.toNat) heap final := by
  induction fuel with
  | zero =>
    intro heap state layout total index finish size represented contents input keysValid outputValid keysSeparate outputSeparate
    have atEnd : state.v4 = count := by omega
    have countNonnegative : 0 ≤ count := by omega
    let next : State_sort_indices := { state with v4 := 0, t11 := false }
    have allContents : Contents keys (Algo2Lean.FiniteIndex.range count) heap layout := by
      simpa [atEnd] using contents
    obtain ⟨final, values, rest, permutation, sorted, output, kept, storage, budget⟩ :=
      extract_loop count count.toNat keys heap next layout (Algo2Lean.FiniteIndex.range count)
        (Algo2Lean.FiniteIndex.range_length _) (Algo2Lean.FiniteIndex.range_nodup _) total
        (by simp [next]) (by dsimp [next]; omega) (by omega) represented allContents outputValid outputSeparate
    refine ⟨final, ?_, ⟨values, permutation, sorted, ?_⟩, storage, ?_⟩
    · intro caller
      apply Reaches.prepend (Step.sort_indices_pc15 _ _ _)
      apply Reaches.prepend (Step.sort_indices_pc14_false _ _ _ (by simp; omega))
      apply Reaches.prepend (Step.sort_indices_pc13 _ _ _)
      simpa [next, show ¬state.v4 < state.v1 by omega] using rest caller
    · simpa [next] using output
    · simpa using budget
  | succ fuel ih =>
    intro heap state layout total index finish size represented contents input keysValid outputValid keysSeparate outputSeparate
    have absent : heap.read layout.positions state.v4 = -1 :=
      represented.indexed.absent state.v4 (by
        have notPresent : ¬0 ≤ heap.read layout.positions state.v4 := by
          intro present
          have := (Algo2Lean.FiniteIndex.range_member _ _).mp ((contents.1 state.v4).mp present)
          omega
        omega)
    obtain ⟨after, call, representedAfter, membership, keyValues, comparisons, swaps, arrays, clocks, storage⟩ :=
      insert_correct (heap.tick "sort_steps") state.v2 layout (queue_tick represented)
        state.v4 (heap.read state.v0 state.v4) absent
    let next := afterInsert state (heap.read state.v0 state.v4)
    let enlarged := { layout with size := layout.size + 1 }
    have nextContents : Contents keys (Algo2Lean.FiniteIndex.range next.v4) after enlarged := by
      constructor
      · intro value
        rw [Algo2Lean.FiniteIndex.range_member]
        change 0 ≤ after.read layout.positions value ↔ _
        rw [membership value]
        change (value = state.v4 ∨ 0 ≤ heap.read layout.positions value) ↔ _
        rw [contents.1 value, Algo2Lean.FiniteIndex.range_member]
        dsimp [next, afterInsert]
        omega
      · intro value present
        change after.read layout.keys value = keys value
        rw [keyValues value]
        by_cases same : value = state.v4
        · subst value
          simp [input]
        · have oldMember : value ∈ Algo2Lean.FiniteIndex.range state.v4 := by
            have := (Algo2Lean.FiniteIndex.range_member _ _).mp present
            apply (Algo2Lean.FiniteIndex.range_member _ _).mpr
            dsimp [next, afterInsert] at this
            omega
          simp [same, contents.2 value oldMember]
    have inputAfter : after.read state.v0 = keys := by
      funext position
      rw [arrays state.v0 keysSeparate.1 keysSeparate.2.1 keysSeparate.2.2 position]
      exact congrFun input position
    obtain ⟨final, rest, correct, frame, budget⟩ := ih after next enlarged total
      (by dsimp [next, afterInsert]; omega) (by dsimp [next, afterInsert]; omega)
      (by dsimp [enlarged, next, afterInsert]; omega) representedAfter nextContents
      inputAfter (by rw [storage.nextRef]; exact keysValid)
      (by rw [storage.nextRef]; exact outputValid) keysSeparate outputSeparate
    have iterationStorage : Storage state.v2
        [layout.vertices, layout.positions, layout.keys, state.v3] heap after :=
      (Storage.tick _ _ _).trans (Storage.of_heap arrays storage clocks)
    have iterationBudget : Budget count 1 heap after :=
      operation_budget (by omega : layout.size ≤ count)
        (Nat.le_trans comparisons (by omega)) (Nat.le_trans swaps (by omega)) clocks
    refine ⟨final, insert_continue heap after final state (by omega) keysValid call rest,
      correct, iterationStorage.trans frame, ?_⟩
    have all := iterationBudget.trans budget
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all

private theorem queue_allocate {heap : Heap} {queue : ObjectRef} {layout : Layout}
    (represented : QueueRep heap queue layout) (contents : Seq) :
    QueueRep (heap.allocate contents) queue layout := by
  have old (ref : SeqRef) (allocated : ref < heap.nextRef) :
      (heap.allocate contents).read ref = heap.read ref := by
    funext index
    simp [Heap.read, Heap.allocate, Nat.ne_of_lt allocated]
  constructor
  · refine ⟨represented.valid.object, represented.valid.readVertices, represented.valid.readPositions,
      represented.valid.readKeys, represented.valid.readSize, ?_, ?_, ?_,
      represented.valid.verticesPositions, represented.valid.verticesKeys, represented.valid.positionsKeys⟩
    all_goals change _ < heap.nextRef + 1
    · exact Nat.lt_succ_of_lt represented.valid.verticesAllocated
    · exact Nat.lt_succ_of_lt represented.valid.positionsAllocated
    · exact Nat.lt_succ_of_lt represented.valid.keysAllocated
  · exact represented.nonnegative
  · rw [old layout.vertices represented.valid.verticesAllocated,
        old layout.positions represented.valid.positionsAllocated]
    exact represented.indexed
  · simpa only [old layout.vertices represented.valid.verticesAllocated,
      old layout.keys represented.valid.keysAllocated] using represented.ordered



private theorem prepared_preserves (heap : Heap) : Preserves heap (preparedHeap heap) := by
  constructor
  · intro ref allocated
    funext index
    have separate : ref ≠ (newHeap heap).nextRef := by
      change ref ≠ heap.nextRef + 3
      omega
    simpa [preparedHeap, Heap.read, Heap.allocate, separate] using new_heap_read_old heap ref index allocated
  · intro ref allocated
    have separate : ref ≠ heap.nextObject := Nat.ne_of_lt allocated
    simp [preparedHeap, newHeap, initializedHeap, set_MinHeap_vertices, set_MinHeap_positions,
      set_MinHeap_keys, set_MinHeap_size, Heap.writeField, Heap.allocateObject, separate]
  · rfl
  · change heap.nextRef ≤ heap.nextRef + 3 + 1; omega
  · change heap.nextObject ≤ heap.nextObject + 1; omega
  · rfl
  · intros; rfl

/-- The complete operational contract: a terminating call returns a fresh array,
    preserves the caller's data, sorts exactly the identifiers, and has a
    logarithmic per-iteration bound on every clock. -/
theorem call (heap : Heap) (keys : SeqRef) (count : Int)
    (allocated : keys < heap.nextRef) (nonnegative : 0 ≤ count) :
    ∃ after result, sort_indices.Call heap (keys, count) after result ∧
      SortedPermutation (heap.read keys) count (after.read result) ∧
      Preserves heap after ∧ heap.nextRef ≤ result ∧ result < after.nextRef ∧
      Budget count (2 * count.toNat) heap after := by
  let prepared := preparedHeap heap
  let result := (newHeap heap).nextRef
  let state : State_sort_indices :=
    { v0 := keys, v1 := count, v2 := heap.nextObject, v3 := result,
      t16 := result, t17 := 0, t18 := heap.nextObject }
  have initial := prepared_preserves heap
  have contents : Contents (heap.read keys) (Algo2Lean.FiniteIndex.range state.v4)
      prepared (emptyLayout heap) := by
    constructor
    · intro value
      have position : prepared.read (emptyLayout heap).positions value = -1 := by
        have separate : (emptyLayout heap).positions ≠ (newHeap heap).nextRef := by
          change heap.nextRef + 1 ≠ heap.nextRef + 3
          omega
        simpa [prepared, preparedHeap, Heap.read, Heap.allocate, separate] using new_heap_positions heap value
      simp [state, position, Algo2Lean.FiniteIndex.range]
    · intro value present
      simp [state, Algo2Lean.FiniteIndex.range] at present
  have keysSeparate : keys ≠ (emptyLayout heap).vertices ∧ keys ≠ (emptyLayout heap).positions ∧
      keys ≠ (emptyLayout heap).keys := by
    exact ⟨Nat.ne_of_lt allocated,
      Nat.ne_of_lt (Nat.lt_of_lt_of_le allocated (Nat.le_add_right _ _)),
      Nat.ne_of_lt (Nat.lt_of_lt_of_le allocated (Nat.le_add_right _ _))⟩
  have outputSeparate : result ≠ (emptyLayout heap).vertices ∧ result ≠ (emptyLayout heap).positions ∧
      result ≠ (emptyLayout heap).keys := by
    change heap.nextRef + 3 ≠ heap.nextRef ∧ heap.nextRef + 3 ≠ heap.nextRef + 1 ∧
      heap.nextRef + 3 ≠ heap.nextRef + 2
    omega
  obtain ⟨after, execution, correct, storage, budget⟩ :=
    insert_loop count count.toNat (heap.read keys) prepared state (emptyLayout heap)
      rfl (by simp [state]) (by dsimp [state]; omega) rfl
      (queue_allocate (new_heap_rep heap) (fun _ => 0)) contents
      (initial.sequences keys allocated) (Nat.lt_of_lt_of_le allocated initial.refs)
      (by change result < result + 1; omega) keysSeparate outputSeparate
  refine ⟨after, result, ⟨allocated, ?_⟩, correct, ?_, ?_, ?_, ?_⟩
  · intro caller
    apply Reaches.prepend (Step.sort_indices_pc28 _ _ _)
    apply (ModuleCall.summary import_0_simulates _ caller (new_heap_summary heap).2).trans
    apply Reaches.prepend (Step.sort_indices_pc27 _ _ _)
    apply Reaches.prepend (Step.sort_indices_pc26 _ _ _)
    apply Reaches.prepend (Step.sort_indices_pc25 _ _ _)
    apply Reaches.prepend (Step.sort_indices_pc24 _ _ _)
    apply Reaches.prepend (Step.sort_indices_pc23 _ _ _)
    exact execution caller
  · constructor
    · intro ref old
      have separate : ref ∉ [(emptyLayout heap).vertices, (emptyLayout heap).positions,
          (emptyLayout heap).keys, result] := by
        change ref ∉ [heap.nextRef, heap.nextRef + 1, heap.nextRef + 2, heap.nextRef + 3]
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        omega
      exact (storage.arrays ref separate).trans (initial.sequences ref old)
    · intro ref old
      exact (storage.objects ref (Nat.ne_of_lt old)).trans (initial.objects ref old)
    · exact storage.collections.trans initial.collections
    · rw [storage.nextRef]; exact initial.refs
    · rw [storage.nextObject]; exact initial.objectRefs
    · exact storage.nextCollection.trans initial.collectionRefs
    · intro name source comparisons swaps
      exact (storage.clocks name source comparisons swaps).trans (initial.clocks name source comparisons swaps)
  · change heap.nextRef ≤ heap.nextRef + 3; omega
  · rw [storage.nextRef]
    change result < result + 1
    omega
  · simpa only [Budget, state, prepared, preparedHeap, Heap.allocate, new_heap_clocks,
      Nat.two_mul] using budget









-- Main result: Correctness


-- Main result: Running time


end SortIndicesAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ (heap : Algo2LeanGenerated.Heap) (keys : Algo2LeanGenerated.SeqRef) (count : Int),
      LT.lt.{0} keys heap.nextRef →
        LE.le.{0} (0 : Int) count →
          Exists.{1} fun after =>
            Exists.{1} fun result =>
              Algo.sort_indices.sort_indices.Call heap (Prod.mk.{0, 0} keys count) after result ∧
                SortIndicesAnalysis.SortedPermutation (heap.read keys) count (after.read result) ∧
                  SortIndicesAnalysis.Preserves heap after ∧
                    LE.le.{0} heap.nextRef result ∧
                      LT.lt.{0} result after.nextRef ∧
                        SortIndicesAnalysis.Budget count (HMul.hMul.{0, 0, 0} (2 : Nat) count.toNat)
                          heap after :=
  SortIndicesAnalysis.call
