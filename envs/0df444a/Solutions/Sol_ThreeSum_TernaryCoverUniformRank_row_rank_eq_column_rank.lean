-- Prove2me | solution 1 for ThreeSum.TernaryCoverUniformRank.row_rank_eq_column_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:45:32.028936+00:00
-- url     : https://prove2.me/submissions/83f70018-7f06-48b3-b1a7-c683c878f747

import Definitions.Def_Submission_ThreeSum_HashFamily
import Definitions.Def_Submission_ThreeSum_TernaryCoverRelations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformRank
import Theorems.Thm_ThreeSum_TernaryCoverUniformRank_mem_relationSpace_columnSpan
import Theorems.Thm_ThreeSum_TernaryCoverUniformRank_relationSpace_finrank_add
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverUniformRank
open Finset TernaryCoverRelations
open scoped BigOperators
variable {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ]
namespace ThreeSum.TernaryCoverUniformRank
theorem _root_.solution {d : ℕ} (v : Fin d → σ → K) :
    Module.finrank K (Submodule.span K (Set.range v)) = Module.finrank K (columnSpan v) := by
  have hker : LinearMap.ker (Fintype.linearCombination K v) = relationSpace (columnSpan v) := by
    ext a
    rw [LinearMap.mem_ker, mem_relationSpace_columnSpan]
    rw [funext_iff]
    simp [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hr := LinearMap.finrank_range_add_finrank_ker (Fintype.linearCombination K v)
  rw [Fintype.range_linearCombination, hker] at hr
  have hc := relationSpace_finrank_add (columnSpan v)
  have hd : Module.finrank K (Fin d → K) = d := by simp
  rw [hd] at hr
  omega
end ThreeSum.TernaryCoverUniformRank
