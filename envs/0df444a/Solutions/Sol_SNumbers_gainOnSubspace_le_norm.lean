-- Prove2me | solution 1 for SNumbers.gainOnSubspace_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:28:20.207678+00:00
-- url     : https://prove2.me/submissions/99f5e192-68b6-424e-90ab-799faeb8c664

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Definitions.Def_SNumbers_Bernstein
public import Theorems.Thm_SNumbers_gainOnSubspace_le_div
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] Submodule.liftQL_mkQL



set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    gainOnSubspace S M ≤ ‖S‖ := by
  by_cases hM : M = ⊥
  · -- gainSet is empty when `M = ⊥`, so `sInf = 0 ≤ ‖S‖`.
    have h_empty : {r : ℝ | ∃ x : X, x ∈ M ∧ x ≠ 0 ∧ r = ‖S x‖ / ‖x‖} = ∅ := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      rintro x ⟨hx_mem, hx_ne, _⟩
      exact hx_ne (by rwa [hM, Submodule.mem_bot] at hx_mem)
    show sInf _ ≤ ‖S‖
    rw [h_empty, Real.sInf_empty]; exact norm_nonneg _
  · obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
    exact (gainOnSubspace_le_div hx_mem hx_ne).trans (S.ratio_le_opNorm x)
end SNumbers
