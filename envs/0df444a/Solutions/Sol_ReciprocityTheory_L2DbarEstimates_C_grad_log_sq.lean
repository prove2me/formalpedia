-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.grad_log_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:26.478877+00:00
-- url     : https://prove2.me/submissions/fcc3c2bb-5349-4e7e-8a13-1d263f5d07cd

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCut
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_norm_sq_clm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal Manifold
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω) (hF : DifferentiableOn ℂ F Ω)
    {z : V n} (hz : z ∈ Ω) (h0 : F z ≠ 0) :
    ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ ^ 2 ≤
      4 * (∑ j, ‖fderiv ℂ F z (EuclideanSpace.basisFun (Fin n) ℂ j)‖ ^ 2) / ‖F z‖ ^ 2 := by
  have hDa : DifferentiableAt ℂ F z := hF.differentiableAt (hΩ.mem_nhds hz)
  have hpos : 0 < ‖F z‖ := norm_pos_iff.mpr h0
  have h1 : HasFDerivAt F ((fderiv ℂ F z).restrictScalars ℝ) z :=
    hDa.hasFDerivAt.restrictScalars ℝ
  have h2 := h1.norm_sq
  have h3 := h2.log (by positivity)
  rw [← norm_sq_clm, h3.fderiv]
  set D := fderiv ℂ F z

  have hM : ‖(‖F z‖ ^ 2)⁻¹ • (2 • (innerSL ℝ (F z)).comp (D.restrictScalars ℝ))‖ ≤
      2 * ‖D‖ / ‖F z‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
    have hi : |inner ℝ (F z) (D h)| ≤ ‖F z‖ * (‖D‖ * ‖h‖) :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (D.le_opNorm h) (norm_nonneg _))
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', innerSL_apply_apply, nsmul_eq_mul, smul_eq_mul,
      Real.norm_eq_abs, abs_mul, abs_inv, Nat.cast_ofNat]
    rw [abs_of_pos (by positivity : (0:ℝ) < ‖F z‖ ^ 2), abs_two]
    calc (‖F z‖ ^ 2)⁻¹ * (2 * |inner ℝ (F z) (D h)|)
        ≤ (‖F z‖ ^ 2)⁻¹ * (2 * (‖F z‖ * (‖D‖ * ‖h‖))) := by gcongr
      _ = 2 * ‖D‖ / ‖F z‖ * ‖h‖ := by field_simp
  calc _ ≤ (2 * ‖D‖ / ‖F z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hM 2
    _ = 4 * ‖D‖ ^ 2 / ‖F z‖ ^ 2 := by ring
end ReciprocityTheory.L2DbarEstimates.C
