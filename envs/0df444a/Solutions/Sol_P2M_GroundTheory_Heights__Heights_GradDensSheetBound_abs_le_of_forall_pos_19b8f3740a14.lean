-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GradDensSheetBound_abs_le_of_forall_pos_19b8f3740a14
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:54:18.833795+00:00
-- url     : https://prove2.me/submissions/8518294d-2e4a-4bff-93a2-f2ce60d1ff62

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGradDensSheetBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.GradDensSheetBound
namespace GroundTheory.Heights₂.Heights.GradDensSheetBound
theorem _root_.solution {X P Q K : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (h : ∀ u : ℝ, 0 < u → 2 * |X| ≤ K * (u * P + u⁻¹ * Q)) :
    |X| ≤ K * Real.sqrt P * Real.sqrt Q := by
  rcases hP.eq_or_lt with hP0 | hPpos
  · rw [← hP0, Real.sqrt_zero, mul_zero, zero_mul]
    by_contra hX
    push Not at hX
    have hkq : 0 ≤ K * Q := mul_nonneg hK hQ
    have hu := h ((K * Q + 1) / |X|) (by positivity)
    rw [← hP0, inv_div, mul_zero, zero_add] at hu
    have e : K * (|X| / (K * Q + 1) * Q) = K * Q * |X| / (K * Q + 1) := by ring
    rw [e, le_div_iff₀ (by positivity)] at hu
    nlinarith
  rcases hQ.eq_or_lt with hQ0 | hQpos
  · rw [← hQ0, Real.sqrt_zero, mul_zero]
    by_contra hX
    push Not at hX
    have hkp : 0 ≤ K * P := mul_nonneg hK hP
    have hu := h (|X| / (K * P + 1)) (by positivity)
    rw [← hQ0, mul_zero, add_zero] at hu
    have e : K * (|X| / (K * P + 1) * P) = K * P * |X| / (K * P + 1) := by ring
    rw [e, le_div_iff₀ (by positivity)] at hu
    nlinarith
  have hp := Real.sqrt_pos.2 hPpos
  have hq := Real.sqrt_pos.2 hQpos
  have hu := h (Real.sqrt Q / Real.sqrt P) (by positivity)
  have sP := Real.mul_self_sqrt hP
  have sQ := Real.mul_self_sqrt hQ
  have e1 : Real.sqrt Q / Real.sqrt P * P = Real.sqrt P * Real.sqrt Q := by
    calc Real.sqrt Q / Real.sqrt P * P = Real.sqrt Q / Real.sqrt P * (Real.sqrt P * Real.sqrt P) := by
          rw [sP]
      _ = Real.sqrt P * Real.sqrt Q := by rw [div_mul_eq_mul_div, div_eq_iff hp.ne']; ring
  have e2 : (Real.sqrt Q / Real.sqrt P)⁻¹ * Q = Real.sqrt P * Real.sqrt Q := by
    calc (Real.sqrt Q / Real.sqrt P)⁻¹ * Q = Real.sqrt P / Real.sqrt Q * (Real.sqrt Q * Real.sqrt Q) := by
          rw [inv_div, sQ]
      _ = Real.sqrt P * Real.sqrt Q := by rw [div_mul_eq_mul_div, div_eq_iff hq.ne']; ring
  have e : Real.sqrt Q / Real.sqrt P * P + (Real.sqrt Q / Real.sqrt P)⁻¹ * Q =
      2 * (Real.sqrt P * Real.sqrt Q) := by rw [e1, e2]; ring
  rw [e] at hu
  linarith
end GroundTheory.Heights₂.Heights.GradDensSheetBound
