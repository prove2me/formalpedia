-- Prove2me | solution 1 for SNumbers.L1Linf.approximationNumber_comp_incl_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:42:56.994561+00:00
-- url     : https://prove2.me/submissions/943c4cfd-ac44-48dd-88e7-ce6d526ab745

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
public import Theorems.Thm_SNumbers_L1Linf_inclL1L2_apply
public import Theorems.Thm_SNumbers_L1Linf_inclL2Linf_apply
public import Theorems.Thm_SNumbers_L1Linf_inclL2Linf_single
public import Theorems.Thm_SNumbers_L1Linf_inner_row
public import Theorems.Thm_P2M_SNumbers_L1Linf_summable_norm_sq_row__73d6b93b43be
public import Theorems.Thm_SNumbers_L1Linf_trunc_coord_of_lt
public import Theorems.Thm_SNumbers_L1Linf_trunc_coord_of_le
public import Theorems.Thm_SNumbers_L1Linf_approximationNumber_comp_incl_comp_trunc_le
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_add_le
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
attribute [local simp] SNumbers.L1Linf.inclL1L2_apply
attribute [local simp] SNumbers.L1Linf.inclL2Linf_apply
attribute [local simp] SNumbers.L1Linf.inclL2Linf_single

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
variable (A : L2 𝕜 →L[𝕜] L1 𝕜) (B : Linf 𝕜 →L[𝕜] L2 𝕜)
namespace SNumbers.L1Linf
theorem _root_.solution (n : ℕ) :
    approximationNumber (B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp A)) n
      ≤ ‖A‖ * ‖B‖ / (n + 1) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- Choose a truncation index beyond which all rows are small.
  set δ := ε / (‖B‖ + 1) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]; positivity
  obtain ⟨m, hm⟩ : ∃ m, ∀ j, m ≤ j → ‖row A j‖ ≤ δ := by
    have h := (summable_norm_sq_row' A).tendsto_atTop_zero
    obtain ⟨m, hm⟩ := Filter.eventually_atTop.mp
      (h.eventually_lt_const (show (0 : ℝ) < δ ^ 2 by positivity))
    refine ⟨m, fun j hj => ?_⟩
    nlinarith [hm j hj, norm_nonneg (row A j), hδpos]
  -- The truncation error is at most `‖B‖ δ ≤ ε`.
  have hres : ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp (A - trunc A m)‖ ≤ δ := by
    refine ContinuousLinearMap.opNorm_le_bound _ hδpos.le fun x => ?_
    refine lp.norm_le_of_forall_le (mul_nonneg hδpos.le (norm_nonneg x)) fun j => ?_
    have hcoord : ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp (A - trunc A m) x) j
        = if j < m then 0 else (inner 𝕜 (row A j) x : 𝕜) := by
      have h : ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp (A - trunc A m) x) j
          = A x j - (trunc A m x) j := by
        simp [ContinuousLinearMap.comp_apply]
      rw [h]
      by_cases hj : j < m
      · rw [if_pos hj, trunc_coord_of_lt A m x hj, sub_self]
      · rw [if_neg hj, trunc_coord_of_le A m x (not_lt.mp hj), sub_zero, inner_row]
    rw [hcoord]
    by_cases hj : j < m
    · rw [if_pos hj, norm_zero]
      exact mul_nonneg hδpos.le (norm_nonneg x)
    · rw [if_neg hj]
      calc ‖(inner 𝕜 (row A j) x : 𝕜)‖ ≤ ‖row A j‖ * ‖x‖ := norm_inner_le_norm _ _
        _ ≤ δ * ‖x‖ :=
            mul_le_mul_of_nonneg_right (hm j (not_lt.mp hj)) (norm_nonneg x)
  -- Subadditivity of the approximation numbers.
  have hsplit : B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp A)
      = B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp (trunc A m))
        + B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp (A - trunc A m)) := by
    ext x
    simp [ContinuousLinearMap.comp_apply, sub_eq_add_neg]
  have hnorm : ‖B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp (A - trunc A m))‖ ≤ ‖B‖ * δ :=
    (B.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left hres (norm_nonneg B))
  have hδB : ‖B‖ * δ ≤ ε :=
    calc ‖B‖ * δ ≤ (‖B‖ + 1) * δ :=
          mul_le_mul_of_nonneg_right (by linarith) hδpos.le
      _ = ε := by rw [hδ]; field_simp
  calc approximationNumber (B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp A)) n
      ≤ approximationNumber (B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp (trunc A m))) n
          + ‖B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp (A - trunc A m))‖ := by
        rw [hsplit]; exact approximationNumber_add_le _ _ n
    _ ≤ ‖A‖ * ‖B‖ / (n + 1) + ε := by
        gcongr
        · exact approximationNumber_comp_incl_comp_trunc_le A B m n
        · exact hnorm.trans hδB
end SNumbers.L1Linf
