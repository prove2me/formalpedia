-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.pow_mul_exp_neg_mul_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:40.335654+00:00
-- url     : https://prove2.me/submissions/6f3ab162-b4ad-439a-8af1-50778a718023

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (n : ℕ) {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    t ^ n * Real.exp (-b * t ^ 2) ≤
      (1 + n.factorial * (2 / b) ^ n) * Real.exp (-(b / 2) * t ^ 2) := by
  have hx : 0 ≤ b / 2 * t ^ 2 := by positivity
  have h1 : 1 ≤ Real.exp (b / 2 * t ^ 2) := Real.one_le_exp hx
  have h2 : (b / 2 * t ^ 2) ^ n / n.factorial ≤ Real.exp (b / 2 * t ^ 2) :=
    Real.pow_div_factorial_le_exp (x := b / 2 * t ^ 2) hx n
  have h3 : t ^ n ≤ 1 + t ^ (2 * n) := by
    rcases le_total t 1 with h | h
    · have : t ^ n ≤ 1 := pow_le_one₀ ht h
      linarith [pow_nonneg ht (2 * n)]
    · have : t ^ n ≤ t ^ (2 * n) := pow_le_pow_right₀ h (by omega)
      linarith
  have h4 : t ^ (2 * n) = (2 / b) ^ n * (b / 2 * t ^ 2) ^ n := by
    rw [pow_mul, ← mul_pow]
    congr 1
    field_simp
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h5 : t ^ (2 * n) ≤ n.factorial * (2 / b) ^ n * Real.exp (b / 2 * t ^ 2) := by
    rw [h4]
    have h2' := (div_le_iff₀ hfac).mp h2
    have hb2 : 0 ≤ (2 / b) ^ n := by positivity
    nlinarith
  have hexp : Real.exp (b / 2 * t ^ 2) * Real.exp (-b * t ^ 2) = Real.exp (-(b / 2) * t ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h6 : t ^ n ≤ (1 + n.factorial * (2 / b) ^ n) * Real.exp (b / 2 * t ^ 2) := by
    nlinarith
  calc t ^ n * Real.exp (-b * t ^ 2)
      ≤ (1 + n.factorial * (2 / b) ^ n) * Real.exp (b / 2 * t ^ 2) * Real.exp (-b * t ^ 2) :=
        mul_le_mul_of_nonneg_right h6 (Real.exp_pos _).le
    _ = (1 + n.factorial * (2 / b) ^ n) * Real.exp (-(b / 2) * t ^ 2) := by
        rw [mul_assoc, hexp]
end ReciprocityTheory.ChartRestriction.G.I2
