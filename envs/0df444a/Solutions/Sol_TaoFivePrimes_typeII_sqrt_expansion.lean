-- Prove2me | solution 1 for TaoFivePrimes.typeII_sqrt_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T05:04:12.253218+00:00
-- url     : https://prove2.me/submissions/58c6d777-972c-4a40-8770-a97d263dc275

import Mathlib

section PartS5E
namespace TaoS5E

theorem sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have hsq : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have h1 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
    have h2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
    have h3 : 0 ≤ Real.sqrt a * Real.sqrt b :=
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
    nlinarith [h1, h2, h3]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt a + Real.sqrt b :=
        Real.sqrt_sq (by positivity)

/-- **Tao, Section 5**: expanding the product in the Type II estimate by
`√(a+b) ≤ √a + √b`. -/
theorem typeII_expand (x W q : ℝ) (hx : 0 < x) (hW : 0 < W) (hq : 0 < q) :
    Real.sqrt (W / 4 + 2 * q) * Real.sqrt (x / (2 * W * q) + 1) * Real.sqrt x
      ≤ (1 / (2 * Real.sqrt 2)) * (x / Real.sqrt q) + (1 / 2) * Real.sqrt (x * W)
        + x / Real.sqrt W + Real.sqrt 2 * Real.sqrt (x * q) := by
  set s : ℝ := Real.sqrt x with hs
  set w : ℝ := Real.sqrt W with hw
  set r : ℝ := Real.sqrt q with hr
  have hs0 : 0 < s := Real.sqrt_pos.mpr hx
  have hw0 : 0 < w := Real.sqrt_pos.mpr hW
  have hr0 : 0 < r := Real.sqrt_pos.mpr hq
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx.le
  have hw2 : w ^ 2 = W := Real.sq_sqrt hW.le
  have hr2 : r ^ 2 = q := Real.sq_sqrt hq.le
  have h20 : (0 : ℝ) < Real.sqrt 2 := by
    have : (0:ℝ) < 2 := by norm_num
    exact Real.sqrt_pos.mpr this
  have h22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  -- the two square roots
  have h1 : Real.sqrt (W / 4 + 2 * q) ≤ w / 2 + Real.sqrt 2 * r := by
    have hle : W / 4 + 2 * q ≤ (w / 2 + Real.sqrt 2 * r) ^ 2 := by
      nlinarith [hw2, hr2, h22, mul_pos hw0 (mul_pos h20 hr0)]
    calc Real.sqrt (W / 4 + 2 * q) ≤ Real.sqrt ((w / 2 + Real.sqrt 2 * r) ^ 2) :=
          Real.sqrt_le_sqrt hle
      _ = w / 2 + Real.sqrt 2 * r := Real.sqrt_sq (by positivity)
  have h2 : Real.sqrt (x / (2 * W * q) + 1) ≤ s / (Real.sqrt 2 * w * r) + 1 := by
    have hden : (0 : ℝ) < Real.sqrt 2 * w * r := by positivity
    have hle : x / (2 * W * q) + 1 ≤ (s / (Real.sqrt 2 * w * r) + 1) ^ 2 := by
      have hxq : x / (2 * W * q) = (s / (Real.sqrt 2 * w * r)) ^ 2 := by
        rw [div_pow, mul_pow, mul_pow, hs2, hw2, hr2, h22]
      rw [hxq]
      nlinarith [div_pos hs0 hden]
    calc Real.sqrt (x / (2 * W * q) + 1) ≤ Real.sqrt ((s / (Real.sqrt 2 * w * r) + 1) ^ 2) :=
          Real.sqrt_le_sqrt hle
      _ = s / (Real.sqrt 2 * w * r) + 1 := Real.sqrt_sq (by positivity)
  -- multiply out
  have hprod : Real.sqrt (W / 4 + 2 * q) * Real.sqrt (x / (2 * W * q) + 1) * Real.sqrt x
      ≤ (w / 2 + Real.sqrt 2 * r) * (s / (Real.sqrt 2 * w * r) + 1) * s := by
    have hA : (0:ℝ) ≤ Real.sqrt (W / 4 + 2 * q) := Real.sqrt_nonneg _
    have hB : (0:ℝ) ≤ Real.sqrt (x / (2 * W * q) + 1) := Real.sqrt_nonneg _
    have hB' : (0:ℝ) ≤ s / (Real.sqrt 2 * w * r) + 1 := by positivity
    have hstep : Real.sqrt (W / 4 + 2 * q) * Real.sqrt (x / (2 * W * q) + 1)
        ≤ (w / 2 + Real.sqrt 2 * r) * (s / (Real.sqrt 2 * w * r) + 1) :=
      mul_le_mul h1 h2 hB (by positivity)
    exact mul_le_mul_of_nonneg_right hstep (le_of_lt hs0)
  refine le_trans hprod (le_of_eq ?_)
  -- identify the four terms
  have hxW : Real.sqrt (x * W) = s * w := Real.sqrt_mul hx.le W
  have hxq : Real.sqrt (x * q) = s * r := Real.sqrt_mul hx.le q
  have hxdivW : x / w = s ^ 2 / w := by rw [hs2]
  have hxdivq : x / r = s ^ 2 / r := by rw [hs2]
  rw [hxW, hxq, hxdivq]
  rw [show x / w = s ^ 2 / w by rw [hs2]]
  field_simp
  ring

end TaoS5E
end PartS5E

theorem solution (x W q : ℝ) (hx : 0 < x) (hW : 0 < W) (hq : 0 < q) :
    Real.sqrt (W / 4 + 2 * q) * Real.sqrt (x / (2 * W * q) + 1) * Real.sqrt x
      ≤ (1 / (2 * Real.sqrt 2)) * (x / Real.sqrt q) + (1 / 2) * Real.sqrt (x * W)
        + x / Real.sqrt W + Real.sqrt 2 * Real.sqrt (x * q) :=
  TaoS5E.typeII_expand x W q hx hW hq
