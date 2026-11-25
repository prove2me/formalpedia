-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.SkodaOperators.pt_Gs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:30:19.39064+00:00
-- url     : https://prove2.me/submissions/67ea1c86-57a2-4ce2-afb6-b017dad555a8

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_WeightedIntegralEqLintegral
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_IntegrableSliceProdFin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H ReciprocityTheory.L2DbarEstimates.H.SkodaOperators
open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open scoped ENNReal InnerProductSpace
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.H.SkodaOperators
theorem _root_.solution {p : ℕ} (g : Fin p → ℂ) (w : ℂ) (c : ℝ) (hN : 0 < vsq g) :
    ∑ i, ‖w * (starRingEnd ℂ) (g i) / ((vsq g : ℝ) : ℂ)‖ ^ 2 * Real.exp (-c) =
      ‖w‖ ^ 2 * Real.exp (-(c + Real.log (vsq g))) := by
  have hexp : Real.exp (-(c + Real.log (vsq g))) = Real.exp (-c) / vsq g := by
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hN, div_eq_mul_inv]
  have hterm : ∀ i, ‖w * (starRingEnd ℂ) (g i) / ((vsq g : ℝ) : ℂ)‖ ^ 2 =
      ‖w‖ ^ 2 * ‖g i‖ ^ 2 / vsq g ^ 2 := by
    intro i
    rw [norm_div, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]
    ring
  have hv : (∑ i, ‖g i‖ ^ 2) = vsq g := rfl
  have hN' : vsq g ≠ 0 := hN.ne'
  rw [hexp]
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Finset.sum_div, ← Finset.mul_sum, hv]
  field_simp
  try ring
end ReciprocityTheory.L2DbarEstimates.H.SkodaOperators
