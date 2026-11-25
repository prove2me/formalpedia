-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.NullS.poly_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:49:04.428805+00:00
-- url     : https://prove2.me/submissions/5ba81f61-0603-409f-aa2b-f8eb604d0b66

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HasFDerivAtEvX
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SquareNormBound
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PolyExpBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.NullS
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.NullS
theorem _root_.solution (c : ℝ) (hc : 0 < c) (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ N * Real.exp (-(c * t ^ 2)) ≤ Real.exp (3 * c) * ((N.factorial : ℝ) / (2 * c) ^ N) := by
  set y := 2 * c * (1 + t) with hy
  have hy0 : 0 ≤ y := by positivity
  have h1 : Real.exp (-(c * t ^ 2)) ≤ Real.exp (3 * c) * Real.exp (-y) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith [sq_nonneg (t - 1)]
  have h2 : (1 + t) ^ N * Real.exp (-y) ≤ (N.factorial : ℝ) / (2 * c) ^ N := by
    have := Real.pow_div_factorial_le_exp y hy0 N
    rw [div_le_iff₀ (by positivity)] at this
    rw [le_div_iff₀ (by positivity)]
    have hyN : y ^ N = (2 * c) ^ N * (1 + t) ^ N := by rw [hy, mul_pow]
    calc (1 + t) ^ N * Real.exp (-y) * (2 * c) ^ N = y ^ N * Real.exp (-y) := by rw [hyN]; ring
      _ ≤ (Real.exp y * N.factorial) * Real.exp (-y) := mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = N.factorial := by rw [mul_comm (Real.exp y), mul_assoc, ← Real.exp_add]; simp
  calc (1 + t) ^ N * Real.exp (-(c * t ^ 2)) ≤ (1 + t) ^ N * (Real.exp (3 * c) * Real.exp (-y)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = Real.exp (3 * c) * ((1 + t) ^ N * Real.exp (-y)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
end PositivityTheory.Rg.Sw.LC.NullS
