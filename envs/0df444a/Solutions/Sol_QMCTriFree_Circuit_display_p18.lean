-- Prove2me | solution 1 for QMCTriFree.Circuit.display_p18
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:53:25.323047+00:00
-- url     : https://prove2.me/submissions/d2ad10d6-7a1a-4417-813b-285c64345a24

import Mathlib
import Definitions.Def_QMCTriFree_Circuit_Algorithm

set_option autoImplicit false

namespace Aux_QMCTriFree_display_p18

noncomputable def cc (n : ℕ) : ℝ :=
  ((Nat.factorial n : ℝ))⁻¹ * (ascPochhammer ℝ n).eval (1 / 2 : ℝ) *
    (ascPochhammer ℝ n).eval (1 / 2 : ℝ) * ((ascPochhammer ℝ n).eval (5 / 2 : ℝ))⁻¹

theorem cc_zero : cc 0 = 1 := by
  simp [cc]

theorem cc_succ (n : ℕ) :
    cc (n + 1) = cc n * ((1 / 2 + (n : ℝ)) ^ 2 / ((5 / 2 + (n : ℝ)) * ((n : ℝ) + 1))) := by
  have h1 : 0 < (ascPochhammer ℝ n).eval (5 / 2 : ℝ) := ascPochhammer_pos n _ (by norm_num)
  have h2 : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h3 : (0 : ℝ) < 5 / 2 + (n : ℝ) := by positivity
  have h4 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  unfold cc
  rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, Nat.factorial_succ]
  push_cast
  field_simp <;> ring

theorem cc_pos (n : ℕ) : 0 < cc n := by
  have h1 : 0 < (ascPochhammer ℝ n).eval (5 / 2 : ℝ) := ascPochhammer_pos n _ (by norm_num)
  have h0 : 0 < (ascPochhammer ℝ n).eval (1 / 2 : ℝ) := ascPochhammer_pos n _ (by norm_num)
  have h2 : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  unfold cc
  exact mul_pos (mul_pos (mul_pos (inv_pos.mpr h2) h0) h0) (inv_pos.mpr h1)

theorem cc_le (n : ℕ) : cc n ≤ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  induction n with
  | zero => rw [cc_zero]; norm_num
  | succ k ih =>
    rw [cc_succ]
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hr : 0 ≤ (1 / 2 + (k : ℝ)) ^ 2 / ((5 / 2 + (k : ℝ)) * ((k : ℝ) + 1)) := by positivity
    calc cc k * ((1 / 2 + (k : ℝ)) ^ 2 / ((5 / 2 + (k : ℝ)) * ((k : ℝ) + 1)))
        ≤ 2 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) *
            ((1 / 2 + (k : ℝ)) ^ 2 / ((5 / 2 + (k : ℝ)) * ((k : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_right ih hr
      _ ≤ 2 / ((((k + 1 : ℕ) : ℝ) + 1) * (((k + 1 : ℕ) : ℝ) + 2)) := by
          push_cast
          rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [pow_nonneg hk 2, pow_nonneg hk 3, pow_nonneg hk 4, pow_nonneg hk 5]

theorem cc_le_one (n : ℕ) : cc n ≤ 1 := by
  refine (cc_le n).trans ?_
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [div_le_one (by positivity)]
  nlinarith

theorem cc_summable (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : Summable (fun n => cc n * t ^ n) := by
  have hg : Summable (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1) ^ 2)) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    push_cast at h
    exact h.mul_left 2
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (cc_pos n).le (pow_nonneg h0 n))
    (fun n => ?_) hg
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  calc cc n * t ^ n ≤ cc n * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ h0 h1) (cc_pos n).le
    _ = cc n := mul_one _
    _ ≤ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := cc_le n
    _ ≤ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
        rw [mul_one_div]
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith

theorem H_eq (t : ℝ) :
    ordinaryHypergeometric (1 / 2 : ℝ) (1 / 2 : ℝ) (5 / 2 : ℝ) t = ∑' n, cc n * t ^ n := by
  rw [ordinaryHypergeometric_eq_tsum]
  rfl

theorem cc1 : cc 1 = 1 / 10 := by
  have h := cc_succ 0
  rw [cc_zero] at h
  norm_num at h
  exact h

theorem cc2 : cc 2 = 9 / 280 := by
  have h := cc_succ 1
  rw [cc1] at h
  norm_num at h
  exact h

theorem cc3 : cc 3 = 5 / 336 := by
  have h := cc_succ 2
  rw [cc2] at h
  norm_num at h
  exact h

theorem cc4 : cc 4 = 35 / 4224 := by
  have h := cc_succ 3
  rw [cc3] at h
  norm_num at h
  exact h

theorem H_lower (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    1 + 1 / 10 * t + 9 / 280 * t ^ 2 + 5 / 336 * t ^ 3 + 35 / 4224 * t ^ 4 ≤
      ordinaryHypergeometric (1 / 2 : ℝ) (1 / 2 : ℝ) (5 / 2 : ℝ) t := by
  rw [H_eq]
  have h := (cc_summable t h0 h1).sum_le_tsum (Finset.range 5)
    (fun n _ => mul_nonneg (cc_pos n).le (pow_nonneg h0 n))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cc_zero, cc1, cc2, cc3, cc4,
    pow_zero, pow_one, one_mul, zero_add] at h
  linarith

theorem H_upper (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1) :
    ordinaryHypergeometric (1 / 2 : ℝ) (1 / 2 : ℝ) (5 / 2 : ℝ) t ≤ (1 - t)⁻¹ := by
  rw [H_eq, ← tsum_geometric_of_lt_one h0 h1]
  refine Summable.tsum_le_tsum (fun n => ?_) (cc_summable t h0 h1.le)
    (summable_geometric_of_lt_one h0 h1)
  calc cc n * t ^ n ≤ 1 * t ^ n := mul_le_mul_of_nonneg_right (cc_le_one n) (pow_nonneg h0 n)
    _ = t ^ n := one_mul _

theorem combine (L L0 B B0 R : ℝ) (hL : L0 ≤ L) (hB : B0 ≤ B) (hL0 : 0 ≤ L0) (hB0 : 0 ≤ B0)
    (hR : R ≤ L0 * B0) : R ≤ L * B :=
  hR.trans (mul_le_mul hL hB hB0 (hL0.trans hL))

theorem cert_hi1 (x : ℝ) (h1 : (0 : ℝ) ≤ x) (h2 : x ≤ ((1 : ℝ) / 2)) :
    (582 / 1000 : ℝ) * (1 + x) ≤ (1 / 2 + 4 / 3 * (10000 / 31416 : ℝ) * ((1 + 2 * x) / 3) * (1 + 1 / 10 * ((1 + 2 * x) / 3) ^ 2 + 9 / 280 * (((1 + 2 * x) / 3) ^ 2) ^ 2 + 5 / 336 * (((1 + 2 * x) / 3) ^ 2) ^ 3 + 35 / 4224 * (((1 + 2 * x) / 3) ^ 2) ^ 4)) * (1 / 2 + 1 / 2 * (1 - (39 / 100 : ℝ) ^ 2 * (1 - x) ^ 2) + 2 * (10000 / 31416 : ℝ) * (39 / 100) * x * ((9208 / 10000 : ℝ) + (1 - (9208 / 10000 : ℝ)) * x)) := by
  have ha : 0 ≤ x - (0 : ℝ) := by linarith
  have hb : 0 ≤ ((1 : ℝ) / 2) - x := by linarith
  have e : (1 / 2 + 4 / 3 * (10000 / 31416 : ℝ) * ((1 + 2 * x) / 3) * (1 + 1 / 10 * ((1 + 2 * x) / 3) ^ 2 + 9 / 280 * (((1 + 2 * x) / 3) ^ 2) ^ 2 + 5 / 336 * (((1 + 2 * x) / 3) ^ 2) ^ 3 + 35 / 4224 * (((1 + 2 * x) / 3) ^ 2) ^ 4)) * (1 / 2 + 1 / 2 * (1 - (39 / 100 : ℝ) ^ 2 * (1 - x) ^ 2) + 2 * (10000 / 31416 : ℝ) * (39 / 100) * x * ((9208 / 10000 : ℝ) + (1 - (9208 / 10000 : ℝ)) * x)) - (582 / 1000 : ℝ) * (1 + x) =
      ((7025745592436 : ℝ) / 281331579375) * (x - (0 : ℝ)) ^ 0 * (((1 : ℝ) / 2) - x) ^ 11 +
      ((258741289076386748 : ℝ) / 1252094327166375) * (x - (0 : ℝ)) ^ 1 * (((1 : ℝ) / 2) - x) ^ 10 +
      ((1203677644981605557 : ℝ) / 1623085238919375) * (x - (0 : ℝ)) ^ 2 * (((1 : ℝ) / 2) - x) ^ 9 +
      ((21881953338538689122 : ℝ) / 14607767150274375) * (x - (0 : ℝ)) ^ 3 * (((1 : ℝ) / 2) - x) ^ 8 +
      ((26938789764793391048 : ℝ) / 14607767150274375) * (x - (0 : ℝ)) ^ 4 * (((1 : ℝ) / 2) - x) ^ 7 +
      ((2276102497884201104 : ℝ) / 1623085238919375) * (x - (0 : ℝ)) ^ 5 * (((1 : ℝ) / 2) - x) ^ 6 +
      ((9776131476214171648 : ℝ) / 14607767150274375) * (x - (0 : ℝ)) ^ 6 * (((1 : ℝ) / 2) - x) ^ 5 +
      ((4167234702075910288 : ℝ) / 14607767150274375) * (x - (0 : ℝ)) ^ 7 * (((1 : ℝ) / 2) - x) ^ 4 +
      ((118629581762158336 : ℝ) / 541028412973125) * (x - (0 : ℝ)) ^ 8 * (((1 : ℝ) / 2) - x) ^ 3 +
      ((6988450159815126944 : ℝ) / 43823301450823125) * (x - (0 : ℝ)) ^ 9 * (((1 : ℝ) / 2) - x) ^ 2 +
      ((247541712312701032 : ℝ) / 3983936495529375) * (x - (0 : ℝ)) ^ 10 * (((1 : ℝ) / 2) - x) ^ 1 +
      ((2241774836680376 : ℝ) / 231869319845625) * (x - (0 : ℝ)) ^ 11 * (((1 : ℝ) / 2) - x) ^ 0 := by ring
  have t0 : 0 ≤ ((7025745592436 : ℝ) / 281331579375) * (x - (0 : ℝ)) ^ 0 * (((1 : ℝ) / 2) - x) ^ 11 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t1 : 0 ≤ ((258741289076386748 : ℝ) / 1252094327166375) * (x - (0 : ℝ)) ^ 1 * (((1 : ℝ) / 2) - x) ^ 10 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t2 : 0 ≤ ((1203677644981605557 : ℝ) / 1623085238919375) * (x - (0 : ℝ)) ^ 2 * (((1 : ℝ) / 2) - x) ^ 9 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t3 : 0 ≤ ((21881953338538689122 : ℝ) / 14607767150274375) * (x - (0 : ℝ)) ^ 3 * (((1 : ℝ) / 2) - x) ^ 8 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t4 : 0 ≤ ((26938789764793391048 : ℝ) / 14607767150274375) * (x - (0 : ℝ)) ^ 4 * (((1 : ℝ) / 2) - x) ^ 7 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t5 : 0 ≤ ((2276102497884201104 : ℝ) / 1623085238919375) * (x - (0 : ℝ)) ^ 5 * (((1 : ℝ) / 2) - x) ^ 6 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t6 : 0 ≤ ((9776131476214171648 : ℝ) / 14607767150274375) * (x - (0 : ℝ)) ^ 6 * (((1 : ℝ) / 2) - x) ^ 5 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t7 : 0 ≤ ((4167234702075910288 : ℝ) / 14607767150274375) * (x - (0 : ℝ)) ^ 7 * (((1 : ℝ) / 2) - x) ^ 4 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t8 : 0 ≤ ((118629581762158336 : ℝ) / 541028412973125) * (x - (0 : ℝ)) ^ 8 * (((1 : ℝ) / 2) - x) ^ 3 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t9 : 0 ≤ ((6988450159815126944 : ℝ) / 43823301450823125) * (x - (0 : ℝ)) ^ 9 * (((1 : ℝ) / 2) - x) ^ 2 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t10 : 0 ≤ ((247541712312701032 : ℝ) / 3983936495529375) * (x - (0 : ℝ)) ^ 10 * (((1 : ℝ) / 2) - x) ^ 1 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t11 : 0 ≤ ((2241774836680376 : ℝ) / 231869319845625) * (x - (0 : ℝ)) ^ 11 * (((1 : ℝ) / 2) - x) ^ 0 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  linarith [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11]

theorem cert_hi2 (x : ℝ) (h1 : ((1 : ℝ) / 2) ≤ x) (h2 : x ≤ (1 : ℝ)) :
    (582 / 1000 : ℝ) * (1 + x) ≤ (1 / 2 + 4 / 3 * (10000 / 31416 : ℝ) * ((1 + 2 * x) / 3) * (1 + 1 / 10 * ((1 + 2 * x) / 3) ^ 2 + 9 / 280 * (((1 + 2 * x) / 3) ^ 2) ^ 2 + 5 / 336 * (((1 + 2 * x) / 3) ^ 2) ^ 3 + 35 / 4224 * (((1 + 2 * x) / 3) ^ 2) ^ 4)) * (1 / 2 + 1 / 2 * (1 - (39 / 100 : ℝ) ^ 2 * (1 - x) ^ 2) + 2 * (10000 / 31416 : ℝ) * (39 / 100) * x * ((9208 / 10000 : ℝ) + (1 - (9208 / 10000 : ℝ)) * x)) := by
  have ha : 0 ≤ x - ((1 : ℝ) / 2) := by linarith
  have hb : 0 ≤ (1 : ℝ) - x := by linarith
  have e : (1 / 2 + 4 / 3 * (10000 / 31416 : ℝ) * ((1 + 2 * x) / 3) * (1 + 1 / 10 * ((1 + 2 * x) / 3) ^ 2 + 9 / 280 * (((1 + 2 * x) / 3) ^ 2) ^ 2 + 5 / 336 * (((1 + 2 * x) / 3) ^ 2) ^ 3 + 35 / 4224 * (((1 + 2 * x) / 3) ^ 2) ^ 4)) * (1 / 2 + 1 / 2 * (1 - (39 / 100 : ℝ) ^ 2 * (1 - x) ^ 2) + 2 * (10000 / 31416 : ℝ) * (39 / 100) * x * ((9208 / 10000 : ℝ) + (1 - (9208 / 10000 : ℝ)) * x)) - (582 / 1000 : ℝ) * (1 + x) =
      ((2241774836680376 : ℝ) / 231869319845625) * (x - ((1 : ℝ) / 2)) ^ 0 * ((1 : ℝ) - x) ^ 11 +
      ((599849175952481096 : ℝ) / 3983936495529375) * (x - ((1 : ℝ) / 2)) ^ 1 * ((1 : ℝ) - x) ^ 10 +
      ((45742271160190933984 : ℝ) / 43823301450823125) * (x - ((1 : ℝ) / 2)) ^ 2 * ((1 : ℝ) - x) ^ 9 +
      ((2288006205306291616 : ℝ) / 541028412973125) * (x - ((1 : ℝ) / 2)) ^ 3 * ((1 : ℝ) - x) ^ 8 +
      ((7748667494504868688 : ℝ) / 695607959536875) * (x - ((1 : ℝ) / 2)) ^ 4 * ((1 : ℝ) - x) ^ 7 +
      ((32611043099511360992 : ℝ) / 1623085238919375) * (x - ((1 : ℝ) / 2)) ^ 5 * ((1 : ℝ) - x) ^ 6 +
      ((4582013504325132112 : ℝ) / 180342804324375) * (x - ((1 : ℝ) / 2)) ^ 6 * ((1 : ℝ) - x) ^ 5 +
      ((4074851802148483288 : ℝ) / 180342804324375) * (x - ((1 : ℝ) / 2)) ^ 7 * ((1 : ℝ) - x) ^ 4 +
      ((834775924982489174 : ℝ) / 60114268108125) * (x - ((1 : ℝ) / 2)) ^ 8 * ((1 : ℝ) - x) ^ 3 +
      ((37605563107813229 : ℝ) / 6679363123125) * (x - ((1 : ℝ) / 2)) ^ 9 * ((1 : ℝ) - x) ^ 2 +
      ((1814106103923104 : ℝ) / 1335872624625) * (x - ((1 : ℝ) / 2)) ^ 10 * ((1 : ℝ) - x) ^ 1 +
      ((65849773001984 : ℝ) / 445290874875) * (x - ((1 : ℝ) / 2)) ^ 11 * ((1 : ℝ) - x) ^ 0 := by ring
  have t0 : 0 ≤ ((2241774836680376 : ℝ) / 231869319845625) * (x - ((1 : ℝ) / 2)) ^ 0 * ((1 : ℝ) - x) ^ 11 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t1 : 0 ≤ ((599849175952481096 : ℝ) / 3983936495529375) * (x - ((1 : ℝ) / 2)) ^ 1 * ((1 : ℝ) - x) ^ 10 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t2 : 0 ≤ ((45742271160190933984 : ℝ) / 43823301450823125) * (x - ((1 : ℝ) / 2)) ^ 2 * ((1 : ℝ) - x) ^ 9 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t3 : 0 ≤ ((2288006205306291616 : ℝ) / 541028412973125) * (x - ((1 : ℝ) / 2)) ^ 3 * ((1 : ℝ) - x) ^ 8 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t4 : 0 ≤ ((7748667494504868688 : ℝ) / 695607959536875) * (x - ((1 : ℝ) / 2)) ^ 4 * ((1 : ℝ) - x) ^ 7 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t5 : 0 ≤ ((32611043099511360992 : ℝ) / 1623085238919375) * (x - ((1 : ℝ) / 2)) ^ 5 * ((1 : ℝ) - x) ^ 6 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t6 : 0 ≤ ((4582013504325132112 : ℝ) / 180342804324375) * (x - ((1 : ℝ) / 2)) ^ 6 * ((1 : ℝ) - x) ^ 5 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t7 : 0 ≤ ((4074851802148483288 : ℝ) / 180342804324375) * (x - ((1 : ℝ) / 2)) ^ 7 * ((1 : ℝ) - x) ^ 4 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t8 : 0 ≤ ((834775924982489174 : ℝ) / 60114268108125) * (x - ((1 : ℝ) / 2)) ^ 8 * ((1 : ℝ) - x) ^ 3 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t9 : 0 ≤ ((37605563107813229 : ℝ) / 6679363123125) * (x - ((1 : ℝ) / 2)) ^ 9 * ((1 : ℝ) - x) ^ 2 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t10 : 0 ≤ ((1814106103923104 : ℝ) / 1335872624625) * (x - ((1 : ℝ) / 2)) ^ 10 * ((1 : ℝ) - x) ^ 1 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t11 : 0 ≤ ((65849773001984 : ℝ) / 445290874875) * (x - ((1 : ℝ) / 2)) ^ 11 * ((1 : ℝ) - x) ^ 0 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  linarith [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11]

theorem cert_mid (x : ℝ) (h1 : ((-1 : ℝ) / 2) ≤ x) (h2 : x ≤ (0 : ℝ)) :
    (582 / 1000 : ℝ) * (1 + x) ≤ (1 / 2 + 4 / 3 * (10000 / 31416 : ℝ) * ((1 + 2 * x) / 3) * (1 + 1 / 10 * ((1 + 2 * x) / 3) ^ 2 + 9 / 280 * (((1 + 2 * x) / 3) ^ 2) ^ 2 + 5 / 336 * (((1 + 2 * x) / 3) ^ 2) ^ 3 + 35 / 4224 * (((1 + 2 * x) / 3) ^ 2) ^ 4)) * (1 / 2 + 1 / 2 * (1 - (39 / 100 : ℝ) ^ 2 * (1 - x) ^ 2) + 2 * (1000000 / 3141592 : ℝ) * (39 / 100) * x * ((9209 / 10000 : ℝ) + (1 - (9209 / 10000 : ℝ)) * x)) := by
  have ha : 0 ≤ x - ((-1 : ℝ) / 2) := by linarith
  have hb : 0 ≤ (0 : ℝ) - x := by linarith
  have e : (1 / 2 + 4 / 3 * (10000 / 31416 : ℝ) * ((1 + 2 * x) / 3) * (1 + 1 / 10 * ((1 + 2 * x) / 3) ^ 2 + 9 / 280 * (((1 + 2 * x) / 3) ^ 2) ^ 2 + 5 / 336 * (((1 + 2 * x) / 3) ^ 2) ^ 3 + 35 / 4224 * (((1 + 2 * x) / 3) ^ 2) ^ 4)) * (1 / 2 + 1 / 2 * (1 - (39 / 100 : ℝ) ^ 2 * (1 - x) ^ 2) + 2 * (1000000 / 3141592 : ℝ) * (39 / 100) * x * ((9209 / 10000 : ℝ) + (1 - (9209 / 10000 : ℝ)) * x)) - (582 / 1000 : ℝ) * (1 + x) =
      ((34551463592 : ℝ) / 245436875) * (x - ((-1 : ℝ) / 2)) ^ 0 * ((0 : ℝ) - x) ^ 11 +
      ((12012750202832312 : ℝ) / 8674475473125) * (x - ((-1 : ℝ) / 2)) ^ 1 * ((0 : ℝ) - x) ^ 10 +
      ((448640292093856 : ℝ) / 72894751875) * (x - ((-1 : ℝ) / 2)) ^ 2 * ((0 : ℝ) - x) ^ 9 +
      ((1272553052135926784 : ℝ) / 78070279258125) * (x - ((-1 : ℝ) / 2)) ^ 3 * ((0 : ℝ) - x) ^ 8 +
      ((2229651906639984976 : ℝ) / 78070279258125) * (x - ((-1 : ℝ) / 2)) ^ 4 * ((0 : ℝ) - x) ^ 7 +
      ((18977068190223730624 : ℝ) / 546491954806875) * (x - ((-1 : ℝ) / 2)) ^ 5 * ((0 : ℝ) - x) ^ 6 +
      ((1483678195613105504 : ℝ) / 49681086800625) * (x - ((-1 : ℝ) / 2)) ^ 6 * ((0 : ℝ) - x) ^ 5 +
      ((2409238972473009978376 : ℝ) / 132797545018070625) * (x - ((-1 : ℝ) / 2)) ^ 7 * ((0 : ℝ) - x) ^ 4 +
      ((1011677743791094244584 : ℝ) / 132797545018070625) * (x - ((-1 : ℝ) / 2)) ^ 8 * ((0 : ℝ) - x) ^ 3 +
      ((27642680208762120051449 : ℝ) / 13146956956788991875) * (x - ((-1 : ℝ) / 2)) ^ 9 * ((0 : ℝ) - x) ^ 2 +
      ((4506073943226061575772 : ℝ) / 13146956956788991875) * (x - ((-1 : ℝ) / 2)) ^ 10 * ((0 : ℝ) - x) ^ 1 +
      ((7025745592436 : ℝ) / 281331579375) * (x - ((-1 : ℝ) / 2)) ^ 11 * ((0 : ℝ) - x) ^ 0 := by ring
  have t0 : 0 ≤ ((34551463592 : ℝ) / 245436875) * (x - ((-1 : ℝ) / 2)) ^ 0 * ((0 : ℝ) - x) ^ 11 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t1 : 0 ≤ ((12012750202832312 : ℝ) / 8674475473125) * (x - ((-1 : ℝ) / 2)) ^ 1 * ((0 : ℝ) - x) ^ 10 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t2 : 0 ≤ ((448640292093856 : ℝ) / 72894751875) * (x - ((-1 : ℝ) / 2)) ^ 2 * ((0 : ℝ) - x) ^ 9 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t3 : 0 ≤ ((1272553052135926784 : ℝ) / 78070279258125) * (x - ((-1 : ℝ) / 2)) ^ 3 * ((0 : ℝ) - x) ^ 8 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t4 : 0 ≤ ((2229651906639984976 : ℝ) / 78070279258125) * (x - ((-1 : ℝ) / 2)) ^ 4 * ((0 : ℝ) - x) ^ 7 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t5 : 0 ≤ ((18977068190223730624 : ℝ) / 546491954806875) * (x - ((-1 : ℝ) / 2)) ^ 5 * ((0 : ℝ) - x) ^ 6 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t6 : 0 ≤ ((1483678195613105504 : ℝ) / 49681086800625) * (x - ((-1 : ℝ) / 2)) ^ 6 * ((0 : ℝ) - x) ^ 5 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t7 : 0 ≤ ((2409238972473009978376 : ℝ) / 132797545018070625) * (x - ((-1 : ℝ) / 2)) ^ 7 * ((0 : ℝ) - x) ^ 4 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t8 : 0 ≤ ((1011677743791094244584 : ℝ) / 132797545018070625) * (x - ((-1 : ℝ) / 2)) ^ 8 * ((0 : ℝ) - x) ^ 3 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t9 : 0 ≤ ((27642680208762120051449 : ℝ) / 13146956956788991875) * (x - ((-1 : ℝ) / 2)) ^ 9 * ((0 : ℝ) - x) ^ 2 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t10 : 0 ≤ ((4506073943226061575772 : ℝ) / 13146956956788991875) * (x - ((-1 : ℝ) / 2)) ^ 10 * ((0 : ℝ) - x) ^ 1 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t11 : 0 ≤ ((7025745592436 : ℝ) / 281331579375) * (x - ((-1 : ℝ) / 2)) ^ 11 * ((0 : ℝ) - x) ^ 0 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  linarith [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11]

theorem cert_low (x : ℝ) (h1 : (-1 : ℝ) ≤ x) (h2 : x ≤ ((-1 : ℝ) / 2)) :
    (582 / 1000 : ℝ) * (1 + x) ≤ (1 / 2 - 4 / 3 * (1000000 / 3141592 : ℝ) * (-(1 + 2 * x) / 3) * (9 / 8)) * (1 / 2 + 1 / 2 * (1 - (39 / 100 : ℝ) ^ 2 * (1 - x) ^ 2) + 2 * (1000000 / 3141592 : ℝ) * (39 / 100) * x * ((9209 / 10000 : ℝ) + (1 - (9209 / 10000 : ℝ)) * x)) := by
  have ha : 0 ≤ x - (-1 : ℝ) := by linarith
  have hb : 0 ≤ ((-1 : ℝ) / 2) - x := by linarith
  have e : (1 / 2 - 4 / 3 * (1000000 / 3141592 : ℝ) * (-(1 + 2 * x) / 3) * (9 / 8)) * (1 / 2 + 1 / 2 * (1 - (39 / 100 : ℝ) ^ 2 * (1 - x) ^ 2) + 2 * (1000000 / 3141592 : ℝ) * (39 / 100) * x * ((9209 / 10000 : ℝ) + (1 - (9209 / 10000 : ℝ)) * x)) - (582 / 1000 : ℝ) * (1 + x) =
      ((255872679509379 : ℝ) / 192765630751250) * (x - (-1 : ℝ)) ^ 0 * (((-1 : ℝ) / 2) - x) ^ 3 +
      ((45444201638413 : ℝ) / 15421250460100) * (x - (-1 : ℝ)) ^ 1 * (((-1 : ℝ) / 2) - x) ^ 2 +
      ((6746299378046887 : ℝ) / 3084250092020000) * (x - (-1 : ℝ)) ^ 2 * (((-1 : ℝ) / 2) - x) ^ 1 +
      ((4318932949 : ℝ) / 7853980000) * (x - (-1 : ℝ)) ^ 3 * (((-1 : ℝ) / 2) - x) ^ 0 := by ring
  have t0 : 0 ≤ ((255872679509379 : ℝ) / 192765630751250) * (x - (-1 : ℝ)) ^ 0 * (((-1 : ℝ) / 2) - x) ^ 3 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t1 : 0 ≤ ((45444201638413 : ℝ) / 15421250460100) * (x - (-1 : ℝ)) ^ 1 * (((-1 : ℝ) / 2) - x) ^ 2 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t2 : 0 ≤ ((6746299378046887 : ℝ) / 3084250092020000) * (x - (-1 : ℝ)) ^ 2 * (((-1 : ℝ) / 2) - x) ^ 1 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  have t3 : 0 ≤ ((4318932949 : ℝ) / 7853980000) * (x - (-1 : ℝ)) ^ 3 * (((-1 : ℝ) / 2) - x) ^ 0 := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ha _)) (pow_nonneg hb _)
  linarith [t0, t1, t2, t3]

end Aux_QMCTriFree_display_p18

set_option maxHeartbeats 1600000 in
open QMCProduct.HalfApprox Matrix MeasureTheory ProbabilityTheory QMCTriFree.Circuit
  Aux_QMCTriFree_display_p18 in
theorem solution :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, (582 / 1000 : ℝ) * (1 + x) ≤ Fβ (39 / 100) x := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  unfold Fβ fGP bracket
  -- constants
  have hpi_lt : Real.pi < 31416 / 10000 := lt_of_lt_of_eq Real.pi_lt_d4 (by norm_num)
  have hpi_gt : 3141592 / 1000000 < Real.pi := lt_of_eq_of_lt (by norm_num) Real.pi_gt_d6
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hk1 : 4 / 3 * (10000 / 31416 : ℝ) ≤ 4 / (3 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hk2 : 4 / (3 * Real.pi) ≤ 4 / 3 * (1000000 / 3141592 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hm1 : 2 * (10000 / 31416 : ℝ) ≤ 2 / Real.pi := by
    rw [le_div_iff₀ hpi0]
    nlinarith
  have hm2 : 2 / Real.pi ≤ 2 * (1000000 / 3141592 : ℝ) := by
    rw [div_le_iff₀ hpi0]
    nlinarith
  have hm0 : 0 ≤ 2 / Real.pi := by positivity
  have hslo : (9208 / 10000 : ℝ) ≤ Real.sqrt (1 - (39 / 100 : ℝ) ^ 2) := by
    have h := Real.sqrt_le_sqrt (show (9208 / 10000 : ℝ) ^ 2 ≤ 1 - (39 / 100 : ℝ) ^ 2 by norm_num)
    rwa [Real.sqrt_sq (by norm_num)] at h
  have hshi : Real.sqrt (1 - (39 / 100 : ℝ) ^ 2) ≤ 9209 / 10000 := by
    have h := Real.sqrt_le_sqrt (show 1 - (39 / 100 : ℝ) ^ 2 ≤ (9209 / 10000 : ℝ) ^ 2 by norm_num)
    rwa [Real.sqrt_sq (by norm_num)] at h
  -- bracket lower bounds
  have hBhi : 0 ≤ x →
      1 / 2 + 1 / 2 * (1 - (39 / 100 : ℝ) ^ 2 * (1 - x) ^ 2) + 2 * (10000 / 31416 : ℝ) * (39 / 100)
          * x * ((9208 / 10000 : ℝ) + (1 - (9208 / 10000 : ℝ)) * x) ≤
        1 / 2 + 1 / 2 * (1 - (39 / 100 : ℝ) ^ 2 * (1 - x) ^ 2) + 2 / Real.pi * (39 / 100) * x *
          (Real.sqrt (1 - (39 / 100 : ℝ) ^ 2) + (1 - Real.sqrt (1 - (39 / 100 : ℝ) ^ 2)) * x) := by
    intro hx0
    have hq0 : 0 ≤ (39 / 100 : ℝ) * x *
        (Real.sqrt (1 - (39 / 100 : ℝ) ^ 2) + (1 - Real.sqrt (1 - (39 / 100 : ℝ) ^ 2)) * x) := by
      have : 0 ≤ Real.sqrt (1 - (39 / 100 : ℝ) ^ 2) * (1 - x) + x :=
        add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith)) hx0
      have h2 : 0 ≤ (39 / 100 : ℝ) * x := by positivity
      nlinarith
    have hqd : 0 ≤ (39 / 100 : ℝ) * x * (1 - x) *
        (Real.sqrt (1 - (39 / 100 : ℝ) ^ 2) - 9208 / 10000) :=
      mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
    nlinarith [mul_nonneg (sub_nonneg.mpr hm1) hq0,
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 * (10000 / 31416)) hqd]
  have hBmid : x ≤ 0 →
      1 / 2 + 1 / 2 * (1 - (39 / 100 : ℝ) ^ 2 * (1 - x) ^ 2) + 2 * (1000000 / 3141592 : ℝ) *
          (39 / 100) * x * ((9209 / 10000 : ℝ) + (1 - (9209 / 10000 : ℝ)) * x) ≤
        1 / 2 + 1 / 2 * (1 - (39 / 100 : ℝ) ^ 2 * (1 - x) ^ 2) + 2 / Real.pi * (39 / 100) * x *
          (Real.sqrt (1 - (39 / 100 : ℝ) ^ 2) + (1 - Real.sqrt (1 - (39 / 100 : ℝ) ^ 2)) * x) := by
    intro hx0
    have hd : 0 ≤ (39 / 100 : ℝ) * ((-x) * (9209 / 10000 - Real.sqrt (1 - (39 / 100 : ℝ) ^ 2)))
        * (1 - x) :=
      mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))) (by linarith)
    have hq1 : 0 ≤ (39 / 100 : ℝ) * ((-x) * ((9209 / 10000 : ℝ) + (1 - (9209 / 10000 : ℝ)) * x)) :=
      mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by nlinarith))
    nlinarith [mul_nonneg hm0 hd, mul_nonneg (sub_nonneg.mpr hm2) hq1]
  have hBmid0 : -1 ≤ x → x ≤ 0 →
      0 ≤ 1 / 2 + 1 / 2 * (1 - (39 / 100 : ℝ) ^ 2 * (1 - x) ^ 2) + 2 * (1000000 / 3141592 : ℝ) *
          (39 / 100) * x * ((9209 / 10000 : ℝ) + (1 - (9209 / 10000 : ℝ)) * x) := by
    intro ha hb
    have e1 : (1 - x) ^ 2 ≤ 4 := by nlinarith
    have e2 : -(9209 / 10000 : ℝ) ≤ x * ((9209 / 10000 : ℝ) + (1 - (9209 / 10000 : ℝ)) * x) := by
      nlinarith
    nlinarith
  rcases le_or_gt 0 x with hx0 | hx0
  · -- region [0, 1]
    have hA : 0 ≤ (1 + 2 * x) / 3 := by linarith
    have ht0 : 0 ≤ ((1 + 2 * x) / 3) ^ 2 := by positivity
    have ht1 : ((1 + 2 * x) / 3) ^ 2 ≤ 1 := by nlinarith
    have hHl := H_lower (((1 + 2 * x) / 3) ^ 2) ht0 ht1
    have hP0 : 0 ≤ 1 + 1 / 10 * ((1 + 2 * x) / 3) ^ 2 + 9 / 280 * (((1 + 2 * x) / 3) ^ 2) ^ 2 +
        5 / 336 * (((1 + 2 * x) / 3) ^ 2) ^ 3 + 35 / 4224 * (((1 + 2 * x) / 3) ^ 2) ^ 4 := by
      positivity
    have hsq : (-(1 + 2 * x) / 3) ^ 2 = ((1 + 2 * x) / 3) ^ 2 := by ring
    rw [hsq]
    have hR := (le_or_gt x (1 / 2)).elim (fun hh => cert_hi1 x hx0 hh) (fun hh => cert_hi2 x hh.le hx2)
    refine combine _ _ _ _ _ ?_ (hBhi hx0) ?_ ?_ hR
    · nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hk1) hA) (le_trans hP0 hHl),
        mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3 * (10000 / 31416)) hA)
          (sub_nonneg.mpr hHl)]
    · have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3 * (10000 / 31416)) hA) hP0
      linarith
    · have e1 : (1 - x) ^ 2 ≤ 1 := by nlinarith
      have e2 : 0 ≤ x * ((9208 / 10000 : ℝ) + (1 - (9208 / 10000 : ℝ)) * x) :=
        mul_nonneg hx0 (by nlinarith)
      linarith
  · rcases le_or_gt (-1 / 2) x with hxm | hxm
    · -- region [-1/2, 0]
      have hA : 0 ≤ (1 + 2 * x) / 3 := by linarith
      have ht0 : 0 ≤ ((1 + 2 * x) / 3) ^ 2 := by positivity
      have ht1 : ((1 + 2 * x) / 3) ^ 2 ≤ 1 := by nlinarith
      have hHl := H_lower (((1 + 2 * x) / 3) ^ 2) ht0 ht1
      have hP0 : 0 ≤ 1 + 1 / 10 * ((1 + 2 * x) / 3) ^ 2 + 9 / 280 * (((1 + 2 * x) / 3) ^ 2) ^ 2 +
          5 / 336 * (((1 + 2 * x) / 3) ^ 2) ^ 3 + 35 / 4224 * (((1 + 2 * x) / 3) ^ 2) ^ 4 := by
        positivity
      have hsq : (-(1 + 2 * x) / 3) ^ 2 = ((1 + 2 * x) / 3) ^ 2 := by ring
      rw [hsq]
      refine combine _ _ _ _ _ ?_ (hBmid hx0.le) ?_ (hBmid0 hx1 hx0.le) (cert_mid x hxm hx0.le)
      · nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hk1) hA) (le_trans hP0 hHl),
          mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3 * (10000 / 31416)) hA)
            (sub_nonneg.mpr hHl)]
      · have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3 * (10000 / 31416)) hA) hP0
        linarith
    · -- region [-1, -1/2]
      have hU : 0 ≤ -(1 + 2 * x) / 3 := by linarith
      have hU1 : -(1 + 2 * x) / 3 ≤ 1 / 3 := by linarith
      have ht0 : 0 ≤ (-(1 + 2 * x) / 3) ^ 2 := by positivity
      have ht1 : (-(1 + 2 * x) / 3) ^ 2 ≤ 1 / 9 := by nlinarith
      have hHu := H_upper ((-(1 + 2 * x) / 3) ^ 2) ht0 (by linarith)
      have hinv : (1 - (-(1 + 2 * x) / 3) ^ 2)⁻¹ ≤ 9 / 8 := by
        rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
        linarith
      have hHl := H_lower ((-(1 + 2 * x) / 3) ^ 2) ht0 (by linarith)
      have hP0 : 0 ≤ 1 + 1 / 10 * (-(1 + 2 * x) / 3) ^ 2 + 9 / 280 * ((-(1 + 2 * x) / 3) ^ 2) ^ 2 +
          5 / 336 * ((-(1 + 2 * x) / 3) ^ 2) ^ 3 + 35 / 4224 * ((-(1 + 2 * x) / 3) ^ 2) ^ 4 := by
        positivity
      have hH0 := le_trans hP0 hHl
      have hH98 := le_trans hHu hinv
      refine combine _ _ _ _ _ ?_ (hBmid hx0.le) ?_ (hBmid0 hx1 hx0.le) (cert_low x hx1 hxm.le)
      · nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hk2) hU) hH0,
          mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3 * (1000000 / 3141592)) hU)
            (sub_nonneg.mpr hH98)]
      · linarith
