-- Prove2me | solution 1 for PackingLPAccel.lemma_5_12
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T15:51:18.462982+00:00
-- url     : https://prove2.me/submissions/56da0d69-168c-4960-8dbb-fd5a4d20d1a1

import Mathlib
import Definitions.Def_PackingLPAccel_Proxy

open PackingLPAccel

namespace PackingLPAccelSol

theorem exp_le_quad (u : ℝ) (hu : |u| ≤ 2) : Real.exp u ≤ 1 + u + 3 / 2 * u ^ 2 := by
  set v := u / 2 with hv
  have hv1 : |v| ≤ 1 := by rw [hv, abs_div]; norm_num; linarith
  have h := Real.abs_exp_sub_one_sub_id_le hv1
  have h2 : Real.exp v ≤ 1 + v + v ^ 2 := by
    have := (abs_le.mp h).2; linarith
  have hpos := (Real.exp_pos v).le
  have hu2 : u = v + v := by rw [hv]; ring
  have he : Real.exp u = Real.exp v * Real.exp v := by rw [hu2, Real.exp_add]
  have hq : 0 ≤ 1 + v + v ^ 2 := by nlinarith [sq_nonneg (v + 1/2)]
  have hm : Real.exp v * Real.exp v ≤ (1 + v + v ^ 2) * (1 + v + v ^ 2) :=
    mul_le_mul h2 h2 hpos hq
  have hvb := abs_le.mp hv1
  have hv2 : v ^ 2 ≤ 1 := by nlinarith
  have key : (1 + v + v ^ 2) * (1 + v + v ^ 2) ≤ 1 + u + 3 / 2 * u ^ 2 := by
    rw [hu2]
    nlinarith [mul_nonneg (sq_nonneg v) (by nlinarith : (0:ℝ) ≤ 3 - 2 * v - v ^ 2)]
  linarith

theorem core (p t : ℝ) (hp : 2 ≤ p) :
    |1 + t| ^ p - 1 - p * t ≤ 2 * p ^ 2 * t ^ 2 + p ^ p * |t| ^ p := by
  have hp0 : 0 ≤ p := by linarith
  have hpp : 0 ≤ p ^ p * |t| ^ p :=
    mul_nonneg (Real.rpow_nonneg hp0 _) (Real.rpow_nonneg (abs_nonneg _) _)
  have hpt2 : 0 ≤ 2 * p ^ 2 * t ^ 2 := by positivity
  have hppt : p ^ p * |t| ^ p = (p * |t|) ^ p := (Real.mul_rpow hp0 (abs_nonneg _)).symm
  by_cases hs : p * |t| ≤ 2
  · have hpt : |p * t| ≤ 2 := by rw [abs_mul, abs_of_nonneg hp0]; exact hs
    have ht1 : |t| ≤ 1 := by
      by_contra hc; push_neg at hc; nlinarith
    have h1t : 0 ≤ 1 + t := by have := (abs_le.mp ht1).1; linarith
    have hle : |1 + t| ≤ Real.exp t := by
      rw [abs_of_nonneg h1t]; linarith [Real.add_one_le_exp t]
    have hr : |1 + t| ^ p ≤ Real.exp (t * p) := by
      rw [Real.exp_mul]; exact Real.rpow_le_rpow (abs_nonneg _) hle hp0
    have he := exp_le_quad (p * t) hpt
    rw [mul_comm t p] at hr
    nlinarith [sq_nonneg (p * t)]
  · push_neg at hs
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg ht] at hs hppt hpp ⊢
      have hle : |1 + t| ≤ p * t := by
        rw [abs_of_nonneg (by linarith)]; nlinarith
      have hr : |1 + t| ^ p ≤ (p * t) ^ p := Real.rpow_le_rpow (abs_nonneg _) hle hp0
      nlinarith [mul_nonneg hp0 ht]
    · rw [abs_of_neg ht] at hs hppt hpp ⊢
      have hq : p * -t ≤ (p * -t) ^ 2 := by nlinarith
      rcases le_or_gt (-1) t with ht1 | ht1
      · have hr : |1 + t| ^ p ≤ 1 :=
          Real.rpow_le_one (abs_nonneg _) (by rw [abs_le]; constructor <;> linarith) hp0
        nlinarith
      · have hle : |1 + t| ≤ p * -t := by
          rw [abs_of_neg (by linarith)]; nlinarith
        have hr : |1 + t| ^ p ≤ (p * -t) ^ p := Real.rpow_le_rpow (abs_nonneg _) hle hp0
        nlinarith

theorem pos_case (p x y : ℝ) (hp : 2 ≤ p) (hx : 0 < x) :
    bregAbs p x y ≤ 2 * p ^ 2 * |x| ^ (p - 2) * y ^ 2 + p ^ p * |y| ^ p := by
  have hp0 : 0 ≤ p := by linarith
  set t := y / x with ht
  have hy : y = x * t := by rw [ht]; field_simp
  have hc := core p t hp
  have hxp : 0 < x ^ p := Real.rpow_pos_of_pos hx p
  unfold bregAbs
  rw [abs_of_pos hx, Real.sign_of_pos hx, hy]
  have e1 : |x + x * t| ^ p = x ^ p * |1 + t| ^ p := by
    rw [show x + x * t = x * (1 + t) by ring, abs_mul, abs_of_pos hx,
      Real.mul_rpow hx.le (abs_nonneg _)]
  have e2 : x ^ (p - 1) = x ^ p / x := Real.rpow_sub_one hx.ne' p
  have e3 : x ^ (p - 2) = x ^ p / x ^ 2 := by
    rw [Real.rpow_sub hx, Real.rpow_two]
  have e4 : |x * t| ^ p = x ^ p * |t| ^ p := by
    rw [abs_mul, abs_of_pos hx, Real.mul_rpow hx.le (abs_nonneg _)]
  rw [e1, e2, e3, e4]
  have hx0 : x ≠ 0 := hx.ne'
  have lhs : x ^ p * |1 + t| ^ p - x ^ p - p * (x ^ p / x) * 1 * (x * t)
      = x ^ p * (|1 + t| ^ p - 1 - p * t) := by field_simp
  have rhs : 2 * p ^ 2 * (x ^ p / x ^ 2) * (x * t) ^ 2 + p ^ p * (x ^ p * |t| ^ p)
      = x ^ p * (2 * p ^ 2 * t ^ 2 + p ^ p * |t| ^ p) := by field_simp
  rw [lhs, rhs]
  exact mul_le_mul_of_nonneg_left hc hxp.le

end PackingLPAccelSol

open PackingLPAccelSol in
theorem solution (p x y : ℝ) (_ : 2 ≤ p) :
    bregAbs p x y ≤ 2 * p ^ 2 * |x| ^ (p - 2) * y ^ 2 + p ^ p * |y| ^ p := by
  rename_i hp
  have hp0 : 0 ≤ p := by linarith
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h := pos_case p (-x) (-y) hp (by linarith)
    have hb : bregAbs p (-x) (-y) = bregAbs p x y := by
      unfold bregAbs
      rw [show -x + -y = -(x + y) by ring, abs_neg, abs_neg, Real.sign_neg]; ring
    rw [hb, abs_neg, abs_neg, neg_sq] at h
    exact h
  · unfold bregAbs
    simp only [zero_add, abs_zero, Real.sign_zero, mul_zero, zero_mul, sub_zero]
    rw [Real.zero_rpow (by linarith)]
    have h1 : 1 ≤ p ^ p := Real.one_le_rpow (by linarith) hp0
    have h2 : 0 ≤ |y| ^ p := Real.rpow_nonneg (abs_nonneg _) _
    have h3 : 0 ≤ 2 * p ^ 2 * (0:ℝ) ^ (p - 2) * y ^ 2 :=
      mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg le_rfl _)) (sq_nonneg _)
    nlinarith
  · exact pos_case p x y hp hx
