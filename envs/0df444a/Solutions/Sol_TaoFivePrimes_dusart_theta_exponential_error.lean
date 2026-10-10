-- Prove2me | solution 1 for TaoFivePrimes.dusart_theta_exponential_error
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T14:32:37.573187+00:00
-- url     : https://prove2.me/submissions/a71f9d31-f2e1-433f-b2ed-c196eb49c9c1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/-
Copyright (c) 2026. Released under Apache 2.0 license.
This is a reduction with two open, source-backed analytic dependencies.
The numerical transfer from psi to theta is proved below using Mathlib.
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

import Theorems.Thm_ExplicitPNT_kadiri_zero_free_region_569693
import Theorems.Thm_ExplicitPNT_dusart_refined_psi_error_of_zero_free_region

set_option maxHeartbeats 800000

namespace DusartReduction

lemma fourth_root_le (u : ℝ) (hu : 0 ≤ u) :
    Real.sqrt (Real.sqrt u) ≤ (3 + u) / 4 := by
  let v := Real.sqrt (Real.sqrt u)
  have hv : 0 ≤ v := Real.sqrt_nonneg _
  have hs := Real.sq_sqrt hu
  have hv2 : v ^ 2 = Real.sqrt u := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hv4 : v ^ 4 = u := by
    calc
      v ^ 4 = (v ^ 2) ^ 2 := by ring
      _ = u := by rw [hv2, hs]
  have hp := mul_nonneg (sq_nonneg (v - 1))
    (show 0 ≤ v ^ 2 + 2 * v + 3 by positivity)
  change v ≤ _
  nlinarith

lemma root_margin (a X : ℝ) (ha : 1 / 2 ≤ a) (hX : 8 ≤ X) :
    Real.sqrt (Real.sqrt (1 - a / X)) ≤ 1 - 1 / (8 * X) := by
  have hXp : 0 < X := by linarith
  have hab : 1 / (2 * X) ≤ a / X := by
    calc
      1 / (2 * X) = (1 / 2) / X := by ring
      _ ≤ a / X := div_le_div_of_nonneg_right ha hXp.le
  have hright : 0 ≤ 1 - 1 / (8 * X) := by
    have : 1 / (8 * X) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    linarith
  by_cases hu : 0 ≤ 1 - a / X
  · have h := fourth_root_le _ hu
    have hid : (3 + (1 - a / X)) / 4 = 1 - (a / X) / 4 := by ring
    rw [hid] at h
    have : 1 / (2 * X) / 4 = 1 / (8 * X) := by ring
    linarith
  · have hz : Real.sqrt (1 - a / X) = 0 :=
      Real.sqrt_eq_zero_of_nonpos (by linarith)
    rw [hz, Real.sqrt_zero]
    exact hright

lemma polynomial_gap (L X : ℝ) (hX : 8 ≤ X) (hL : 5 * X ^ 2 ≤ L) :
    16 * L * X ≤ Real.exp (L / 2 - X) := by
  have hXp : 0 < X := by linarith
  have hX2 : 64 ≤ X ^ 2 := by nlinarith
  have hLpos : 0 < L := by nlinarith
  have hXL : 4 * X ≤ L := by nlinarith
  have hX3 : 512 ≤ X ^ 3 := by
    nlinarith [mul_nonneg (show 0 ≤ X - 8 by linarith) (show 0 ≤ X ^ 2 + 8 * X + 64 by positivity)]
  have hL2 : 6144 * X ≤ L ^ 2 := by
    have hp := mul_nonneg (show 0 ≤ L - 5 * X ^ 2 by linarith)
      (show 0 ≤ L + 5 * X ^ 2 by positivity)
    have hq := mul_nonneg (show 0 ≤ 25 * X ^ 3 - 6144 by nlinarith) hXp.le
    nlinarith
  have hp := mul_nonneg (show 0 ≤ L ^ 2 - 6144 * X by linarith) hLpos.le
  have hexp := Real.pow_div_factorial_le_exp (L / 4) (show 0 ≤ L / 4 by positivity) 3
  norm_num [Nat.factorial] at hexp
  calc
    16 * L * X ≤ (L / 4) ^ 3 / 6 := by nlinarith
    _ ≤ Real.exp (L / 4) := hexp
    _ ≤ Real.exp (L / 2 - X) := Real.exp_le_exp.mpr (by linarith)

lemma prime_power_margin (x X : ℝ) (hx : 0 < x) (hX : 8 ≤ X)
    (hL : 5 * X ^ 2 ≤ Real.log x) :
    |Chebyshev.psi x - Chebyshev.theta x| ≤
      (x * Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X)) / (8 * X) := by
  have hXp : 0 < X := by linarith
  have hLpos : 0 < Real.log x := by nlinarith
  have hxone : 1 ≤ x := (Real.log_pos_iff hx.le).mp hLpos |>.le
  have hsqrt : Real.sqrt x = Real.exp (Real.log x / 2) := by
    rw [Real.exp_half, Real.exp_log hx]
  have hpoly := polynomial_gap (Real.log x) X hX hL
  have hmul := mul_le_mul_of_nonneg_right hpoly (Real.exp_pos (Real.log x / 2)).le
  have hexp : Real.exp (Real.log x / 2 - X) * Real.exp (Real.log x / 2) =
      x * Real.exp (-X) := by
    rw [← Real.exp_add]
    have : Real.log x / 2 - X + Real.log x / 2 = Real.log x + -X := by ring
    rw [this, Real.exp_add, Real.exp_log hx]
  rw [hexp] at hmul
  have hsmall : 2 * Real.sqrt x * Real.log x ≤ x * Real.exp (-X) / (8 * X) := by
    apply (le_div_iff₀ (by positivity : 0 < 8 * X)).2
    rw [hsqrt]
    nlinarith only [hmul]
  have hc : 1 ≤ Real.sqrt (8 / Real.pi) := by
    apply Real.one_le_sqrt.mpr
    apply (le_div_iff₀ Real.pi_pos).2
    linarith [Real.pi_le_four]
  have hxs : 1 ≤ Real.sqrt X := Real.one_le_sqrt.mpr (by linarith)
  have hcs : 1 ≤ Real.sqrt (8 / Real.pi) * Real.sqrt X := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hxs)]
  have htop : x * Real.exp (-X) ≤
      x * Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X) := by
    have hm := mul_le_mul_of_nonneg_left hcs (mul_pos hx (Real.exp_pos (-X))).le
    nlinarith only [hm]
  calc
    |Chebyshev.psi x - Chebyshev.theta x| ≤ 2 * Real.sqrt x * Real.log x :=
      Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hxone
    _ ≤ x * Real.exp (-X) / (8 * X) := hsmall
    _ ≤ _ := div_le_div_of_nonneg_right htop (by positivity)

lemma theta_of_refined_psi (x X : ℝ) (hx : 0 < x) (hX : 8 ≤ X)
    (hL : 5 * X ^ 2 ≤ Real.log x)
    (hpsi : |Chebyshev.psi x - x| <
      x * Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X) *
        Real.sqrt (Real.sqrt (1 - (Real.log (2 * Real.pi) - 1 / 2) / X))) :
    |Chebyshev.theta x - x| <
      x * Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X) := by
  let A := x * Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have hlogpi : (1 : ℝ) ≤ Real.log (2 * Real.pi) := hlog4.trans
    (Real.log_le_log (by norm_num) (by linarith [Real.two_le_pi]))
  have hroot := root_margin (Real.log (2 * Real.pi) - 1 / 2) X (by linarith) hX
  have hmargin := mul_le_mul_of_nonneg_left hroot hA
  have hd := prime_power_margin x X hx hX hL
  have habs : |Chebyshev.theta x - x| ≤
      |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := by
    have h := abs_add_le (Chebyshev.psi x - x) (Chebyshev.theta x - Chebyshev.psi x)
    rw [show Chebyshev.psi x - x + (Chebyshev.theta x - Chebyshev.psi x) =
      Chebyshev.theta x - x by ring] at h
    simpa only [abs_sub_comm (Chebyshev.theta x) (Chebyshev.psi x)] using h
  change |Chebyshev.psi x - x| < A * _ at hpsi
  change |Chebyshev.psi x - Chebyshev.theta x| ≤ A / (8 * X) at hd
  change |Chebyshev.theta x - x| < A
  have hid : A * (1 - 1 / (8 * X)) + A / (8 * X) = A := by ring
  linarith

end DusartReduction

theorem solution
    (x : ℝ) (hx : 0 < x)
    (hlog : 70 * (569693 / 100000 : ℝ) ≤ Real.log x) :
    |Chebyshev.theta x - x| <
      x * Real.sqrt (8 / Real.pi) *
        Real.sqrt (Real.sqrt (Real.log x / (569693 / 100000 : ℝ))) *
        Real.exp (-Real.sqrt (Real.log x / (569693 / 100000 : ℝ))) := by
  let R : ℝ := 569693 / 100000
  let X := Real.sqrt (Real.log x / R)
  have hR : 0 < R := by norm_num [R]
  have hdiv : 70 ≤ Real.log x / R := (le_div_iff₀ hR).2 hlog
  have hsq : X ^ 2 = Real.log x / R := Real.sq_sqrt (by linarith)
  have hXnonneg : 0 ≤ X := Real.sqrt_nonneg _
  have hXsq : 70 ≤ X ^ 2 := by rw [hsq]; exact hdiv
  have hX836 : (836 / 100 : ℝ) < X := by nlinarith
  have hX8 : 8 ≤ X := by linarith
  have hthreshold : max (836 / 100 : ℝ) (8 / R) < X := by
    apply max_lt_iff.mpr
    exact ⟨hX836, lt_trans (by norm_num [R] : 8 / R < 836 / 100) hX836⟩
  have hL : 5 * X ^ 2 ≤ Real.log x := by
    have hsq' : X ^ 2 * R = Real.log x := (eq_div_iff hR.ne').mp hsq
    have hR5 : 5 ≤ R := by norm_num [R]
    nlinarith [mul_nonneg (sub_nonneg.mpr hR5) (sq_nonneg X)]
  have hzero : ∀ s : ℂ, 2 * Real.pi < |s.im| →
      1 - 1 / (R * Real.log |s.im|) < s.re → riemannZeta s ≠ 0 := by
    intro s hs hσ
    exact ExplicitPNT.kadiri_zero_free_region_569693 s
      (by linarith [Real.two_le_pi]) hσ.le
  have hpsi := ExplicitPNT.dusart_refined_psi_error_of_zero_free_region
    R hR hzero x hx hthreshold
  exact DusartReduction.theta_of_refined_psi x X hx hX8 hL hpsi
