-- Prove2me | solution 1 for ThreeSum.TernaryOriginalSpan.mem_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:13:04.520083+00:00
-- url     : https://prove2.me/submissions/bac3b297-3bb0-49a1-a00a-7b45c1ac4baf

import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpan
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalSpan
variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V]
namespace ThreeSum.TernaryOriginalSpan
theorem _root_.solution (rows : List V) (v : V) :
    v ∈ values K rows ↔ v ∈ Submodule.span K {w | w ∈ rows} := by
  induction rows generalizing v with
  | nil => simp [values]
  | cons row rows ih =>
    have hset : {w | w ∈ row::rows} = insert row {w | w ∈ rows} := by
      ext w
      simp only [Set.mem_setOf_eq,Set.mem_insert_iff,List.mem_cons]
    rw [hset]
    refine Iff.trans ?_ (Submodule.mem_span_insert (R := K) (x := v) (y := row)
      (s := {w | w ∈ rows})).symm
    simp only [values,List.mem_flatMap,List.mem_map,Finset.mem_toList,Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨a,w,hw,rfl⟩
      exact ⟨a,w,(ih w).mp hw,rfl⟩
    · rintro ⟨a,w,hw,rfl⟩
      exact ⟨a,w,(ih w).mpr hw,rfl⟩
end ThreeSum.TernaryOriginalSpan
