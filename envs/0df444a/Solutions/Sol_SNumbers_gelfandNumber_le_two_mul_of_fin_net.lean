-- Prove2me | solution 1 for SNumbers.gelfandNumber_le_two_mul_of_fin_net
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:18:43.223562+00:00
-- url     : https://prove2.me/submissions/6e28c427-bc1a-4bc7-80b2-77098761c41a

module
public import Definitions.Def_SNumbers_Entropy
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_SVD
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Definitions.Def_SNumbers_EntropyBounds
public import Theorems.Thm_ContinuousLinearMap_opNorm_le_of_unit_closedBall
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
public import Theorems.Thm_SNumbers_entropyNumber_zero_op
public import Theorems.Thm_SNumbers_exists_closed_codim_forall_eq_zero
public import Theorems.Thm_SNumbers_gelfandNumber_le_deviation
public import Theorems.Thm_SNumbers_padFin_apply
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
attribute [local simp] SNumbers.entropyNumber_zero_op
attribute [local simp] SNumbers.padFin_apply
attribute [local simp] Submodule.liftQL_mkQL



set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers
theorem _root_.solution {S : X →L[𝕜] Y} {k : ℕ} {y : Fin k → Y}
    {ε : ℝ} (hcov : ∀ x : X, ‖x‖ ≤ 1 → ∃ i, ‖S x - y i‖ ≤ ε) :
    gelfandNumber S k ≤ 2 * ε := by
  classical
  choose b hb_norm hb_app using fun i : Fin k => exists_dual_vector'' 𝕜 (y i)
  obtain ⟨M, hM_closed, hM_rank, hM_ker⟩ := exists_closed_codim_forall_eq_zero S b
  refine (gelfandNumber_le_deviation hM_closed hM_rank).trans ?_
  show ‖S.comp M.subtypeL‖ ≤ 2 * ε
  refine ContinuousLinearMap.opNorm_le_of_unit_closedBall _ fun z hz => ?_
  obtain ⟨i, hi⟩ := hcov (z : X) (by simpa using hz)
  -- The norming functional of `y i` vanishes on `S x`, so `‖y i‖` is small.
  have h_yi : ‖y i‖ ≤ ε := by
    have h0 : b i (S (z : X)) = 0 := hM_ker (z : X) z.2 i
    have heq : b i (y i - S (z : X)) = ((‖y i‖ : ℝ) : 𝕜) := by
      rw [map_sub, hb_app i, h0, sub_zero]
    have hnorm : ‖y i‖ = ‖b i (y i - S (z : X))‖ := by
      rw [heq, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    rw [hnorm]
    calc ‖b i (y i - S (z : X))‖
        ≤ ‖b i‖ * ‖y i - S (z : X)‖ := (b i).le_opNorm _
      _ ≤ 1 * ‖y i - S (z : X)‖ :=
          mul_le_mul_of_nonneg_right (hb_norm i) (norm_nonneg _)
      _ = ‖S (z : X) - y i‖ := by rw [one_mul, norm_sub_rev]
      _ ≤ ε := hi
  calc ‖(S.comp M.subtypeL) z‖
      = ‖S (z : X)‖ := by simp
    _ ≤ ‖S (z : X) - y i‖ + ‖y i‖ := by
        simpa using norm_add_le (S (z : X) - y i) (y i)
    _ ≤ ε + ε := add_le_add hi h_yi
    _ = 2 * ε := by ring
end SNumbers
