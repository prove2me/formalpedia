-- Prove2me | solution 1 for ThreeSum.TernaryOriginalSpanCatalog.mem_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:19:50.051202+00:00
-- url     : https://prove2.me/submissions/c626de07-4430-45a6-bca2-0d432bd85f7a

import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpan
import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpanCatalog
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalSpanCatalog
open Finset
set_option maxHeartbeats 2000000
variable {p J : ℕ}
namespace ThreeSum.TernaryOriginalSpanCatalog
theorem _root_.solution [Fact p.Prime] (rows : List (Fin J → ZMod p)) (v : Fin J → ZMod p) :
    v∈values p rows ↔ v∈Submodule.span (ZMod p) {w | w∈rows} := by
  induction rows generalizing v with
  | nil => simp [values]
  | cons row rows ih =>
    have hs : {w | w∈row::rows}=insert row {w | w∈rows} := by
      ext w
      simp only [Set.mem_setOf_eq,Set.mem_insert_iff,List.mem_cons]
    rw [hs]
    refine Iff.trans ?_ (Submodule.mem_span_insert (R := ZMod p) (x := v) (y := row)
      (s := {w | w∈rows})).symm
    simp only [values,List.mem_flatMap,List.mem_map,List.mem_range]
    constructor
    · rintro ⟨a,ha,w,hw,rfl⟩
      exact ⟨(a : ZMod p),w,(ih w).mp hw,rfl⟩
    · rintro ⟨a,w,hw,he⟩
      refine ⟨a.val,ZMod.val_lt a,w,(ih w).mpr hw,?_⟩
      simpa only [ZMod.natCast_zmod_val] using he.symm
end ThreeSum.TernaryOriginalSpanCatalog
