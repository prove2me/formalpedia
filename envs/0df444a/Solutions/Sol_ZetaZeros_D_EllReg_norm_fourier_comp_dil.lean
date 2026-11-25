-- Prove2me | solution 1 for ZetaZeros.D.EllReg.norm_fourier_comp_dil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:06:41.836109+00:00
-- url     : https://prove2.me/submissions/4e3229f4-bb23-4461-849c-dfdf83ddf0f0

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace ZetaZeros.D.EllReg
theorem _root_.solution (c : V → ℂ) (r : ℝ) (hr : 0 < r) (x0 w : V) :
    ‖𝓕 (fun x => c (r⁻¹ • (x - x0))) w‖ = r ^ Module.finrank ℝ V * ‖𝓕 c (r • w)‖ := by
  have hrw : ∀ y : V, Complex.exp (↑(-2 * Real.pi * inner ℝ (r • y + x0) w) * Complex.I) • c y =
      Complex.exp (↑(-2 * Real.pi * inner ℝ x0 w) * Complex.I) *
        (Complex.exp (↑(-2 * Real.pi * inner ℝ y (r • w)) * Complex.I) • c y) := by
    intro y
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
    congr 2
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_right]
    push_cast
    ring
  rw [Real.fourier_eq', Real.fourier_eq']
  have h1 : (∫ v : V, Complex.exp (↑(-2 * Real.pi * inner ℝ v w) * Complex.I) • c (r⁻¹ • (v - x0))) =
      ∫ v : V, (fun y => Complex.exp (↑(-2 * Real.pi * inner ℝ (r • y + x0) w) * Complex.I) • c y)
        (r⁻¹ • v) := by
    rw [← MeasureTheory.integral_add_right_eq_self _ x0]
    congr 1
    funext v
    simp only [add_sub_cancel_right, smul_inv_smul₀ hr.ne']
  have h2 := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (MeasureTheory.volume : MeasureTheory.Measure V)
    (fun y => Complex.exp (↑(-2 * Real.pi * inner ℝ (r • y + x0) w) * Complex.I) • c y) hr.le
  rw [h1.trans h2]
  simp only [hrw]
  rw [MeasureTheory.integral_const_mul, norm_smul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
end ZetaZeros.D.EllReg
