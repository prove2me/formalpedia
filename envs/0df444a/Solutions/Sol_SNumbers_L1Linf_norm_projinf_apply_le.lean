-- Prove2me | solution 1 for SNumbers.L1Linf.norm_projinf_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:32:44.48266+00:00
-- url     : https://prove2.me/submissions/d62d03a0-dae6-457e-910d-e3442fa5c1b3

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_LittleGrothendieck
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_AddOns_Approximable
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Sequences
public import Definitions.Def_SNumbers_Examples_IdentityL1Linfty
public import Theorems.Thm_SNumbers_L1Linf_incl_apply
public import Theorems.Thm_SNumbers_L1Linf_e_apply_self
public import Theorems.Thm_SNumbers_L1Linf_projinf_coord
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_SNumbers_signedSum_empty
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] John.rankOneSA_apply
attribute [local simp] SNumbers.Complexification.adjoint_complexify
attribute [local simp] SNumbers.Complexification.complexify_conj
attribute [local simp] SNumbers.Complexification.complexify_fst
attribute [local simp] SNumbers.Complexification.complexify_ofReal
attribute [local simp] SNumbers.Complexification.complexify_snd
attribute [local simp] SNumbers.Complexification.norm_complexify
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] SNumbers.padFin_apply
attribute [local simp] SNumbers.signedSum_empty
attribute [local simp] Submodule.liftQL_mkQL


attribute [local simp] SNumbers.L1Linf.incl_apply
attribute [local simp] SNumbers.L1Linf.e_apply_self

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
namespace SNumbers.L1Linf
theorem _root_.solution (m : ℕ) (y : Linf 𝕜) :
    ‖(projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)) y‖ ≤ Real.sqrt m * ‖y‖ := by
  have hnn : (0 : ℝ) ≤ ‖(projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)) y‖ := norm_nonneg _
  have hsq : ‖(projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)) y‖ ^ 2
      = ∑ j : Fin m, ‖y (j : ℕ)‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
    exact Finset.sum_congr rfl fun j _ => by rw [projinf_coord]
  have hle : ∑ j : Fin m, ‖y (j : ℕ)‖ ^ 2 ≤ (m : ℝ) * ‖y‖ ^ 2 := by
    calc ∑ j : Fin m, ‖y (j : ℕ)‖ ^ 2
        ≤ ∑ _j : Fin m, ‖y‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => by gcongr; exact lp.norm_apply_le_norm (by simp) y (j : ℕ)
      _ = (m : ℝ) * ‖y‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have key : ‖(projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)) y‖ ^ 2
      ≤ (Real.sqrt m * ‖y‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (m : ℝ)), hsq]; exact hle
  exact le_of_sq_le_sq key (by positivity)
end SNumbers.L1Linf
