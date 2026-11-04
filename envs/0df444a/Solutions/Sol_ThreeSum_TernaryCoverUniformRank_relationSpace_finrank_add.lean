-- Prove2me | solution 1 for ThreeSum.TernaryCoverUniformRank.relationSpace_finrank_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:44:34.899957+00:00
-- url     : https://prove2.me/submissions/347fd1ab-3eb4-4842-ab7d-b7cd848a8238

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_TernaryCoverRelations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformRank
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverUniformRank
open Finset TernaryCoverRelations
open scoped BigOperators
variable {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]
namespace ThreeSum.TernaryCoverUniformRank
theorem _root_.solution {d : ℕ} (S : Submodule K (Fin d → K)) :
    Module.finrank K S + Module.finrank K (relationSpace S) = d := by
  let e := dotProductEquiv K (Fin d)
  have hdim := LinearEquiv.finrank_eq (e.symm.submoduleMap S.dualAnnihilator)
  have heq : S.dualAnnihilator.map e.symm.toLinearMap = relationSpace S := by
    simpa [relationSpace, e] using S.dualAnnihilator.map_equiv_eq_comap_symm e.symm
  rw [heq] at hdim
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq S
  rw [hdim] at h
  simpa using h
end ThreeSum.TernaryCoverUniformRank
