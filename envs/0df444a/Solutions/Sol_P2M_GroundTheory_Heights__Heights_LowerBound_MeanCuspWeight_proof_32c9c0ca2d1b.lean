-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBound_MeanCuspWeight_proof_32c9c0ca2d1b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:08:01.620136+00:00
-- url     : https://prove2.me/submissions/74d6c5fc-dedd-40e3-871f-e47827749f94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PMeanCuspWeight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBound_max_zero_add_le_of_nonneg_b2974e2bf39a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBound
open Real MeasureTheory Filter Topology
noncomputable section
namespace GroundTheory.Heights₂.Heights.LowerBound
namespace MeanCuspWeight
theorem _root_.solution : MeanCuspWeight.Statement := by
  intro X _ μ U lam f j' vr rd h
  have := h.isProbability
  have hf : (1 : ℝ) ≤ f := by exact_mod_cast h.one_le_f
  have hj : (1 : ℝ) ≤ j' := by exact_mod_cast h.one_le_j'
  have hfj : 0 ≤ (f : ℝ) * j' := by positivity
  have hvr0 : 0 < vr := lt_of_lt_of_le one_pos h.one_le_vr
  have hlogvr : 0 ≤ log vr := Real.log_nonneg h.one_le_vr
  have hr0 : 0 < vr ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hvr0 _
  have hlogr : log (vr ^ (-(1 / 2 : ℝ))) = -(1 / 2) * log vr := Real.log_rpow hvr0 _

  have key : ∀ z, max 0 (log (1 / lam z)) ≤
      max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) + 1 / 2 * log vr := by
    intro z
    have hl := h.lam_pos z
    have e : log (1 / lam z) = log (vr ^ (-(1 / 2 : ℝ)) / lam z) + 1 / 2 * log vr := by
      rw [Real.log_div one_ne_zero hl.ne', Real.log_div hr0.ne' hl.ne', hlogr, Real.log_one]
      ring
    rw [e]
    exact max_zero_add_le_of_nonneg (by positivity)
  set L : ℝ := log (2 * f * j' * rd) with hL
  set g : X → ℝ := fun z =>
    (f : ℝ) * j' * (2 * (max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) + 1 / 2 * log vr) + L) with hg
  have hUg : ∀ z, U z ≤ g z := by
    intro z
    refine (h.U_le z).trans (mul_le_mul_of_nonneg_left ?_ hfj)
    linarith [key z]
  have hint_h := h.logPlus_integrable
  have hint : Integrable g μ :=
    (((hint_h.add (integrable_const (1 / 2 * log vr))).const_mul 2).add
      (integrable_const L)).const_mul _
  have hmono : ∫ z, U z ∂μ ≤ ∫ z, g z ∂μ :=
    integral_mono_of_nonneg (ae_of_all _ h.U_nonneg) hint (ae_of_all _ hUg)
  have hval : ∫ z, g z ∂μ = (f : ℝ) * j' *
      (2 * ((∫ z, max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) ∂μ) + 1 / 2 * log vr) + L) := by
    have h1 : Integrable (fun z => max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) + 1 / 2 * log vr) μ :=
      hint_h.add (integrable_const _)
    have h2 : Integrable
        (fun z => 2 * (max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) + 1 / 2 * log vr)) μ :=
      h1.const_mul 2
    rw [hg, integral_const_mul, integral_add h2 (integrable_const L), integral_const_mul,
      integral_add hint_h (integrable_const _), integral_const, integral_const, probReal_univ,
      one_smul, one_smul]
  rw [hval] at hmono
  refine hmono.trans (mul_le_mul_of_nonneg_left ?_ hfj)
  linarith [h.logPlus_mean]
end MeanCuspWeight
end GroundTheory.Heights₂.Heights.LowerBound
