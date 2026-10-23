-- Prove2me | solution 1 for PersPricingDist.UniformA.up_profit_14
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T18:56:42.201988+00:00
-- url     : https://prove2.me/submissions/285f3f40-b8ec-4d1d-93e2-91545000cd4e

import Mathlib
import Definitions.Def_PersPricingDist_UniformA_Setting

open PersPricingDist.UniformA MeasureTheory

namespace PPD1UP14

lemma lin_integral (c d a b : ℝ) :
    ∫ x in a..b, (c + d * x) = c * (b - a) + d * ((b ^ 2 - a ^ 2) / 2) := by
  have hi : IntervalIntegrable (fun x : ℝ => d * x) volume a b :=
    (continuous_const_mul d).intervalIntegrable a b
  rw [intervalIntegral.integral_add intervalIntegrable_const hi]
  rw [intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  simp [smul_eq_mul]; ring

end PPD1UP14

open PPD1UP14 in
theorem solution (M : Model) (hM : M.Standing) :
    M.indUP M.wUP (M.pA_UP M.wUP) =
      (M.s + 2 * M.s ^ 2 - 4 * M.v * M.s - 2 * M.v * M.s ^ 2 +
        2 * M.v ^ 2 + M.v ^ 2 * M.s) /
        (4 * M.s * (1 - M.s ^ 2)) := by
  have hs := hM.s_pos
  have hsv := hM.s_lt_v
  have hv1 := hM.v_lt_one
  have h1s : 0 < 1 - M.s := by linarith
  have hX : M.v ≤ M.s * M.X := by
    have := hM.market_large
    rw [div_le_iff₀ hs] at this; linarith
  set w := M.wUP with hw_def
  set a := M.pA_UP w with ha_def
  have ha : a = w + (1 - M.v) / 2 := rfl
  have hw' : w * (2 * (1 + M.s)) = M.s * (1 + M.v) := by
    rw [hw_def]; unfold Model.wUP; field_simp
  have hw0 : 0 < w := by nlinarith
  set xc := (1 - M.v) / (2 * (1 - M.s)) with hxc_def
  set xB := (M.v - w) / M.s with hxB_def
  have hxc' : (1 - M.s) * xc = 1 - M.v - a + w := by rw [hxc_def, ha]; field_simp; ring
  have hxB' : M.s * xB = M.v - w := by rw [hxB_def]; field_simp
  have hxc0 : 0 < xc := by rw [hxc_def]; apply div_pos <;> linarith
  -- ordering 0 < xc < 1 - a < xB ≤ X
  have hcxh : xc < 1 - a := by
    have : (1 - M.s) * xc < (1 - M.s) * (1 - a) := by rw [hxc', ha]; nlinarith
    exact lt_of_mul_lt_mul_left this h1s.le
  have hxhB : 1 - a < xB := by
    have : M.s * (1 - a) < M.s * xB := by rw [hxB', ha]; nlinarith
    exact lt_of_mul_lt_mul_left this hs.le
  have hBX : xB ≤ M.X := by
    have : M.s * xB ≤ M.s * M.X := by linarith
    exact le_of_mul_le_mul_left this hs
  have ha0 : 0 < a := by rw [ha]; linarith
  have hsx1 : ∀ x, x < xB → 0 ≤ M.v - M.s * x := by
    intro x hx
    have : M.s * x < M.s * xB := mul_lt_mul_of_pos_left hx hs
    linarith
  -- pointwise description of the payment
  have p1 : ∀ x, 0 < x → x < xc → M.paidUP w a x = a := by
    intro x hx0 hx1
    have hcx : (1 - M.s) * x < (1 - M.s) * xc := mul_lt_mul_of_pos_left hx1 h1s
    have hnB : ¬ M.buysB_UP w a x := by
      simp only [Model.buysB_UP, Model.uA, Model.uB, not_lt]
      rw [max_eq_left (by linarith : (0:ℝ) ≤ 1 - x), max_eq_left (hsx1 x (by linarith)),
        max_eq_left (by linarith : (0:ℝ) ≤ 1 - x - a)]
      linarith
    have hA : a ≤ M.uA x := by
      simp only [Model.uA]; rw [max_eq_left (by linarith : (0:ℝ) ≤ 1 - x)]; linarith
    rw [Model.paidUP, if_neg hnB, if_pos hA]
  have p2 : ∀ x, xc < x → x < 1 - a → M.paidUP w a x = (M.v - 1 + a) + (1 - M.s) * x := by
    intro x hx0 hx1
    have hcx : (1 - M.s) * xc < (1 - M.s) * x := mul_lt_mul_of_pos_left hx0 h1s
    have e1 : M.uA x = 1 - x := by simp only [Model.uA]; rw [max_eq_left (by linarith)]
    have e2 : M.uB x = M.v - M.s * x := by
      simp only [Model.uB]; rw [max_eq_left (hsx1 x (by linarith))]
    have hB : M.buysB_UP w a x := by
      simp only [Model.buysB_UP]
      rw [e1, e2, max_eq_left (by linarith : (0:ℝ) ≤ 1 - x - a)]
      linarith
    rw [Model.paidUP, if_pos hB, Model.pB_UP, e1, e2, max_eq_left (by linarith : (0:ℝ) ≤ 1 - x - a)]
    ring
  have p3 : ∀ x, 1 - a < x → x < xB → M.paidUP w a x = M.v + (-M.s) * x := by
    intro x hx0 hx1
    have hsxB : M.s * x < M.s * xB := mul_lt_mul_of_pos_left hx1 hs
    have e2 : M.uB x = M.v - M.s * x := by
      simp only [Model.uB]; rw [max_eq_left (hsx1 x hx1)]
    have e3 : max (M.uA x - a) 0 = 0 := by
      apply max_eq_right
      simp only [Model.uA]
      rcases le_total (1 - x) 0 with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    have hB : M.buysB_UP w a x := by
      simp only [Model.buysB_UP]
      rw [e2, e3]
      linarith
    rw [Model.paidUP, if_pos hB, Model.pB_UP, e2, e3]
    ring
  have p4 : ∀ x, xB < x → M.paidUP w a x = 0 := by
    intro x hx0
    have hsxB : M.s * xB < M.s * x := mul_lt_mul_of_pos_left hx0 hs
    have hnB : ¬ M.buysB_UP w a x := by
      simp only [Model.buysB_UP, not_lt]
      have : M.uB x ≤ w := by
        simp only [Model.uB]
        apply max_le <;> linarith
      have := le_max_right (M.uA x - a) 0
      linarith
    have hnA : ¬ a ≤ M.uA x := by
      simp only [Model.uA, not_le]
      apply max_lt <;> linarith
    rw [Model.paidUP, if_neg hnB, if_neg hnA]
  unfold Model.indUP
  have c1 : Continuous (fun _ : ℝ => a) := continuous_const
  have c2 : Continuous (fun x : ℝ => (M.v - 1 + a) + (1 - M.s) * x) := by fun_prop
  have c3 : Continuous (fun x : ℝ => M.v + (-M.s) * x) := by fun_prop
  have c4 : Continuous (fun _ : ℝ => (0:ℝ)) := continuous_const
  have e1 : Set.EqOn (fun _ : ℝ => a) (M.paidUP w a) (Set.uIoo 0 xc) := by
    rw [Set.uIoo_of_le hxc0.le]; intro x ⟨h0, h1⟩; exact (p1 x h0 h1).symm
  have e2 : Set.EqOn (fun x : ℝ => (M.v - 1 + a) + (1 - M.s) * x) (M.paidUP w a)
      (Set.uIoo xc (1 - a)) := by
    rw [Set.uIoo_of_le hcxh.le]; intro x ⟨h0, h1⟩; exact (p2 x h0 h1).symm
  have e3 : Set.EqOn (fun x : ℝ => M.v + (-M.s) * x) (M.paidUP w a) (Set.uIoo (1 - a) xB) := by
    rw [Set.uIoo_of_le hxhB.le]; intro x ⟨h0, h1⟩; exact (p3 x h0 h1).symm
  have e4 : Set.EqOn (fun _ : ℝ => (0:ℝ)) (M.paidUP w a) (Set.uIoo xB M.X) := by
    rw [Set.uIoo_of_le hBX]; intro x ⟨h0, _⟩; exact (p4 x h0).symm
  have i1 := (c1.intervalIntegrable (μ := volume) 0 xc).congr_uIoo e1
  have i2 := (c2.intervalIntegrable (μ := volume) xc (1 - a)).congr_uIoo e2
  have i3 := (c3.intervalIntegrable (μ := volume) (1 - a) xB).congr_uIoo e3
  have i4 := (c4.intervalIntegrable (μ := volume) xB M.X).congr_uIoo e4
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 (i2.trans (i3.trans i4)),
    ← intervalIntegral.integral_add_adjacent_intervals i2 (i3.trans i4),
    ← intervalIntegral.integral_add_adjacent_intervals i3 i4]
  rw [← intervalIntegral.integral_congr_uIoo e1, ← intervalIntegral.integral_congr_uIoo e2,
    ← intervalIntegral.integral_congr_uIoo e3, ← intervalIntegral.integral_congr_uIoo e4]
  rw [lin_integral, lin_integral]
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_zero, add_zero]
  rw [ha, hxc_def, hxB_def]
  have hw : w = M.s * (1 + M.v) / (2 * (1 + M.s)) := rfl
  rw [hw]
  have h1s' : 1 - M.s ≠ 0 := by linarith
  have h1s'' : 1 + M.s ≠ 0 := by linarith
  have h1s2 : 1 - M.s ^ 2 ≠ 0 := by nlinarith
  field_simp
  ring
