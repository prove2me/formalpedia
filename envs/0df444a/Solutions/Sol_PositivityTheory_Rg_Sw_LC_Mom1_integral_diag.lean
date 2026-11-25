-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Mom1.integral_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:45:32.342016+00:00
-- url     : https://prove2.me/submissions/a434a237-ac73-4f54-b9e8-e3dcbfa8c9d2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_OneMom
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_IntegrableRpowGauss

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Real
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Mom1
namespace PositivityTheory.Rg.Sw.LC.Mom1
theorem _root_.solution (c : ℝ) (hc : 0 < c) (p : ℕ) :
    ∫ z : ℂ, z ^ p * star z ^ p * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ)) =
      ((Real.pi * (p.factorial : ℝ) / c ^ (p + 1) : ℝ) : ℂ) := by
  have e : ∀ z : ℂ, z ^ p * star z ^ p * Complex.exp ((-(c * ‖z‖ ^ 2) : ℝ)) =
      ((‖z‖ ^ ((2 * p : ℕ) : ℝ) * Real.exp (-c * ‖z‖ ^ (2 : ℝ)) : ℝ) : ℂ) := by
    intro z
    rw [← mul_pow, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Real.rpow_natCast,
      Real.rpow_two]
    push_cast
    rw [pow_mul]
    ring_nf
  simp_rw [e]
  rw [integral_complex_ofReal, Complex.integral_rpow_mul_exp_neg_mul_rpow (by norm_num)
    (by have : (0 : ℝ) ≤ ((2 * p : ℕ) : ℝ) := by positivity
        linarith) hc]
  congr 1
  have h1 : ((((2 * p : ℕ) : ℝ) + 2) / 2) = (p : ℝ) + 1 := by push_cast; ring
  rw [h1, show (-(((2 * p : ℕ) : ℝ) + 2) / 2) = -((p : ℝ) + 1) by push_cast; ring,
    Real.Gamma_nat_eq_factorial, Real.rpow_neg hc.le, show ((p : ℝ) + 1) = ((p + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]
  field_simp
end PositivityTheory.Rg.Sw.LC.Mom1
