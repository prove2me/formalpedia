-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P56.hybrid_derivative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:43:06.810973+00:00
-- url     : https://prove2.me/submissions/0b6ce4df-75e3-4ebd-ac17-9cacce392805

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section


open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Section VI C, p.15, Eq.(54): the derivative in the nonconstant interior regime.
Here s is the square root; its radical is displaced by text extraction. -/
theorem solution (q qprime x : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hqp : 0 < qprime ∧ qprime < 1)
    (hx : 0 < x ∧ x < 1 / 2) :
    let a := binaryConvolution x q
    let s := Real.sqrt (1 - 16 * qprime * (1 - qprime) * x * (1 - x))
    HasDerivAt (hybridFormula q qprime)
      ((1 - 2 * q) * Real.log ((1 - a) / a) -
        4 * qprime * (1 - qprime) * (1 - 2 * x) / s * Real.log ((1 + s) / (1 - s))) x := by
  intro a s
  obtain ⟨hq0, hq1⟩ := hq; obtain ⟨hp0, hp1⟩ := hqp; obtain ⟨hx0, hx1⟩ := hx
  have hk0 : 0 < qprime * (1 - qprime) := mul_pos hp0 (by linarith)
  have hk1 : qprime * (1 - qprime) ≤ 1 / 4 := by nlinarith [sq_nonneg (2 * qprime - 1)]
  have hxx0 : 0 < x * (1 - x) := mul_pos hx0 (by linarith)
  have hxx1 : x * (1 - x) < 1 / 4 := by nlinarith [sq_nonneg (2 * x - 1)]
  have hu0 : 0 < 1 - 16 * qprime * (1 - qprime) * x * (1 - x) := by
    have : qprime * (1 - qprime) * (x * (1 - x)) < 1 / 16 := by
      calc qprime * (1 - qprime) * (x * (1 - x)) ≤ 1 / 4 * (x * (1 - x)) :=
            mul_le_mul_of_nonneg_right hk1 hxx0.le
        _ < 1 / 4 * (1 / 4) := by linarith
        _ = 1 / 16 := by norm_num
    nlinarith
  have hu1 : 1 - 16 * qprime * (1 - qprime) * x * (1 - x) < 1 := by nlinarith [mul_pos hk0 hxx0]
  have hs0 : 0 < s := Real.sqrt_pos.2 hu0
  have hs1 : s < 1 := by
    show Real.sqrt _ < 1
    rw [Real.sqrt_lt' one_pos]; linarith
  have hss : s ^ 2 = 1 - 16 * qprime * (1 - qprime) * x * (1 - x) := Real.sq_sqrt hu0.le
  have ha0 : 0 < a := by
    show 0 < x * (1 - q) + (1 - x) * q
    rcases eq_or_lt_of_le hq0 with h | h
    · subst h; simp; linarith
    · have : 0 < (1 - x) * q := mul_pos (by linarith) h
      nlinarith [mul_nonneg hx0.le (sub_nonneg.2 hq1)]
  have ha1 : a < 1 := by
    show x * (1 - q) + (1 - x) * q < 1
    rcases eq_or_lt_of_le hq1 with h | h
    · subst h; simp; linarith
    · have : 0 < x * (1 - q) := mul_pos hx0 (by linarith)
      nlinarith [mul_nonneg (sub_nonneg.2 hx1.le) hq0]
  have hconv : HasDerivAt (fun y => binaryConvolution y q) (1 - 2 * q) x := by
    have : (fun y => binaryConvolution y q) = fun y => q + (1 - 2 * q) * y := by
      funext y; unfold binaryConvolution; ring
    rw [this]
    simpa using ((hasDerivAt_id' x).const_mul (1 - 2 * q)).const_add q
  have hA := (Real.hasDerivAt_binEntropy ha0.ne' ha1.ne).comp x hconv
  have hU : HasDerivAt (fun y => 1 - 16 * qprime * (1 - qprime) * y * (1 - y))
      (-(16 * qprime * (1 - qprime) * (1 - 2 * x))) x := by
    have h := (((hasDerivAt_id' x).const_mul (16 * qprime * (1 - qprime))).mul
      ((hasDerivAt_id' x).const_sub 1)).const_sub 1
    exact h.congr_deriv (by ring)
  have hS := hU.sqrt hu0.ne'
  have hG := (hS.const_sub 1).div_const 2
  have hg0 : (1 - s) / 2 ≠ 0 := by intro h; linarith
  have hg1 : (1 - s) / 2 ≠ 1 := by intro h; linarith
  have hB := (Real.hasDerivAt_binEntropy hg0 hg1).comp x hG
  have hT := hA.sub hB
  have e1 : Real.log ((1 - a) / a) = Real.log (1 - a) - Real.log a :=
    Real.log_div (by linarith) ha0.ne'
  have e2 : Real.log ((1 + s) / (1 - s)) = Real.log (1 + s) - Real.log (1 - s) :=
    Real.log_div (by linarith) (by linarith)
  have e3 : Real.log (1 - (1 - s) / 2) = Real.log (1 + s) - Real.log 2 := by
    rw [show 1 - (1 - s) / 2 = (1 + s) / 2 by ring]; exact Real.log_div (by linarith) two_ne_zero
  have e4 : Real.log ((1 - s) / 2) = Real.log (1 - s) - Real.log 2 :=
    Real.log_div (by linarith) two_ne_zero
  have key : (Real.log (1 - a) - Real.log a) * (1 - 2 * q) -
      (Real.log (1 - (1 - s) / 2) - Real.log ((1 - s) / 2)) *
        (-(-(16 * qprime * (1 - qprime) * (1 - 2 * x)) / (2 * s)) / 2) =
      (1 - 2 * q) * Real.log ((1 - a) / a) -
        4 * qprime * (1 - qprime) * (1 - 2 * x) / s * Real.log ((1 + s) / (1 - s)) := by
    rw [e1, e2, e3, e4]
    field_simp
    ring
  exact hT.congr_deriv key



end

