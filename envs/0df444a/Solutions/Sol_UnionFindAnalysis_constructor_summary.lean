-- Prove2me | solution 1 for UnionFindAnalysis.constructor_summary
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:54:57.496456+00:00
-- url     : https://prove2.me/submissions/a68afb27-55b8-4d99-9d37-bd932f272779

import Definitions.Def_Algo_union_find_init_Analysis


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













/-- The named initialization loop writes every remaining parent pointer and
    returns beneath any caller; its preconditions describe only the local state. -/
theorem initialize_remaining (count : Nat) (state : Configuration)
    (object : Ref_UnionFind) (parent : SeqRef) (first : Int)
    (location : UnionFind.__init__.At.init_loop state)
    (readObject : UnionFind.__init__.Local.self state = some object)
    (readFirst : UnionFind.__init__.Local.vertex state = some first)
    (readBound : UnionFind.__init__.Local.size state = some (first + (count : Int)))
    (readParent : field_UnionFind_parent state.heap object = some parent)
    (allocated : parent < state.heap.nextRef) :
    UnionFind.__init__.CallFrom state (initializeEntries state.heap parent first count) () := by
  induction count generalizing state first with
  | zero =>
    cases state with
    | done => cases location
    | active heap frame originalStack =>
      cases frame with
      | invalid => cases location
      | fn_UnionFind_find => cases location
      | fn_UnionFind_union => cases location
      | fn_UnionFind => cases location
      | fn_UnionFind___init__ pc s =>
        have counter : pc = 4 := by
          unfold UnionFind.__init__.At.init_loop at location
          split at location <;> simp_all
        subst pc
        simp only [Config.heap] at readParent allocated
        simp [UnionFind.__init__.Local.self, UnionFind.__init__.Local.vertex,
          UnionFind.__init__.Local.size] at readObject readFirst readBound
        intro caller
        apply Reaches.prepend (Step.UnionFind___init___pc4 _ _ _)
        apply Reaches.prepend (Step.UnionFind___init___pc3_false _ _ _
          (by simp only [decide_eq_false_iff_not]; omega))
        apply Reaches.prepend (Step.UnionFind___init___pc2 _ _ _)
        exact Reaches.single (Step.UnionFind___init___pc1 _ _ _)
  | succ count ih =>
    cases state with
    | done => cases location
    | active heap frame originalStack =>
      cases frame with
      | invalid => cases location
      | fn_UnionFind_find => cases location
      | fn_UnionFind_union => cases location
      | fn_UnionFind => cases location
      | fn_UnionFind___init__ pc s =>
        have counter : pc = 4 := by
          unfold UnionFind.__init__.At.init_loop at location
          split at location <;> simp_all
        subst pc
        simp only [Config.heap] at readParent allocated
        simp [UnionFind.__init__.Local.self, UnionFind.__init__.Local.vertex,
          UnionFind.__init__.Local.size] at readObject readFirst readBound
        have next := ih
          (.active ((heap.write parent s.v2 s.v2).tick "uf_init")
            (.fn_UnionFind___init__ 4 { s with t4 := decide (s.v2 < s.v1), v2 := s.v2 + 1 })
            originalStack) (first + 1) True.intro
          (by simpa [UnionFind.__init__.Local.self] using readObject)
          (by simp [UnionFind.__init__.Local.vertex, readFirst])
          (by simp [UnionFind.__init__.Local.size]; omega)
          readParent allocated
        intro caller
        apply Reaches.prepend (Step.UnionFind___init___pc4 _ _ _)
        apply Reaches.prepend (Step.UnionFind___init___pc3_true _ _ _
          (by simp only [decide_eq_true_eq]; omega))
        apply Reaches.prepend (Step.UnionFind___init___pc7 _ _ _
          (by simpa [readObject, readParent] using allocated))
        apply Reaches.prepend (Step.UnionFind___init___pc6 _ _ _)
        apply Reaches.prepend (Step.UnionFind___init___pc5 _ _ _)
        simpa [Config.heap, initializeEntries, readFirst, readObject, readParent] using next caller





















/-- Initialization executes the source assignments and the complete named loop. -/
theorem initialization_summary (heap : Heap) (object : Ref_UnionFind) (size : Nat)
    (valid : is_UnionFind heap object) :
    UnionFind.__init__.Call heap (object, (size : Int)) (initializedHeap heap object size) () := by
  refine ⟨valid, ?_⟩
  intro caller
  apply Reaches.prepend (Step.UnionFind___init___pc18 _ _ _)
  apply Reaches.prepend (Step.UnionFind___init___pc17 _ _ _)
  apply Reaches.prepend (Step.UnionFind___init___pc16 _ _ _)
  apply Reaches.prepend (Step.UnionFind___init___pc15 _ _ _ (by simpa [is_UnionFind] using valid))
  apply Reaches.prepend (Step.UnionFind___init___pc14 _ _ _)
  apply Reaches.prepend (Step.UnionFind___init___pc13 _ _ _)
  apply Reaches.prepend (Step.UnionFind___init___pc12 _ _ _)
  apply Reaches.prepend (Step.UnionFind___init___pc11 _ _ _
    (by simpa [is_UnionFind, set_UnionFind_parent] using valid))
  apply Reaches.prepend (Step.UnionFind___init___pc10 _ _ _
    (by simpa [is_UnionFind, set_UnionFind_parent, set_UnionFind_rank] using valid))
  apply Reaches.prepend (Step.UnionFind___init___pc9 _ _ _)
  apply Reaches.prepend (Step.UnionFind___init___pc8 _ _ _)
  have loop := initialize_remaining size
    (.active ((prepareInitialHeap heap object size).tick "uf_init")
      (.fn_UnionFind___init__ 4 { v0 := object, v1 := size, v2 := 0, t5 := heap.nextRef + 1, t6 := object, t8 := heap.nextRef, t9 := object }) caller)
    object heap.nextRef 0 True.intro rfl rfl (by simp [UnionFind.__init__.Local.size])
    (prepareInitialHeap_parent heap object size valid) (by
      change heap.nextRef < (prepareInitialHeap heap object size).nextRef
      simp)
  simpa [initializedHeap, prepareInitialHeap, set_UnionFind_parent] using! loop caller

/-- The public constructor always terminates on a natural size. -/
theorem constructor_summary (heap : Heap) (size : Nat) :
    UnionFind.Call heap (size : Int) (newHeap heap size) heap.nextObject := by
  have allocated : is_UnionFind (heap.allocateObject "union_find.UnionFind") heap.nextObject := by
    simp [is_UnionFind]
  refine ⟨True.intro, ?_⟩
  intro caller
  apply Reaches.prepend (Step.UnionFind_pc7 _ _ _)
  apply Reaches.prepend (Step.UnionFind_pc6 _ _ _)
  apply Reaches.prepend (Step.UnionFind_pc5 _ _ _)
  apply Reaches.prepend (Step.UnionFind_pc4 _ _ _)
  apply Reaches.prepend (Step.UnionFind_pc3 _ _ _)
  apply Reaches.trans ((initialization_summary _ _ size allocated).2 _)
  apply Reaches.prepend (Step.UnionFind_pc2 _ _ _)
  exact Reaches.single (Step.UnionFind_pc1 _ _ _ (initializedHeap_valid _ _ size allocated))





















-- Main result: Correctness and running time













end UnionFindAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ (heap : Algo2LeanGenerated.Heap) (size : Nat),
      Algo.union_find.UnionFind.Call heap (↑size : Int) (UnionFindAnalysis.newHeap heap size)
        heap.nextObject :=
  UnionFindAnalysis.constructor_summary
