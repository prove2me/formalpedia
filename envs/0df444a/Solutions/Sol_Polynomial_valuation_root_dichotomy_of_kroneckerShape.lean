-- Prove2me | solution 1 for Polynomial.valuation_root_dichotomy_of_kroneckerShape
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c6ca2a40-93e4-52f3-a1d7-6286cec31977

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_valuation_root_dichotomy_of_kroneckerShape

set_option autoImplicit false

open Polynomial

theorem solution
    {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
    {q : ℕ} (hq : 1 < q) (x₀ c : K) (hx : 1 < v x₀) (hc : v c ≤ 1)
    (H : K[X]) (hHdeg : H.natDegree ≤ q)
    (hHb : ∀ b < q, v (H.coeff b) ≤ v x₀ ^ q) (hHq : v (H.coeff q) ≤ v x₀ ^ (q - 1))
    (y : K) (hy : ((C (x₀ ^ q) - X) * (C x₀ - X ^ q) + C c * H).IsRoot y) :
    (v y = v x₀ ^ q ∧ v (y - x₀ ^ q) ≤ v c * v x₀ ^ (q - 1)) ∨
      (v y ^ q = v x₀ ∧ v (x₀ - y ^ q) ≤ v c * v y ^ (q - 1)) := by
  have hx0 : x₀ ≠ 0 := fun h => by simp [h] at hx
  have hX0 : 0 < v x₀ := lt_trans zero_lt_one hx
  have hX1 : 1 ≤ v x₀ := hx.le
  have hq0 : q ≠ 0 := by omega
  have hq1 : q - 1 < q := by omega
  have hqq : q = (q - 1) + 1 := by omega

  have hroot : (x₀ ^ q - y) * (x₀ - y ^ q) = -(c * H.eval y) := by
    have h := hy.eq_zero
    simp only [eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_pow] at h
    linear_combination h
  have hE : v (x₀ ^ q - y) * v (x₀ - y ^ q) ≤ v (H.eval y) := by
    rw [← map_mul, hroot, Valuation.map_neg, map_mul]
    exact mul_le_of_le_one_left zero_le' hc
  have hE' : v (x₀ ^ q - y) * v (x₀ - y ^ q) = v c * v (H.eval y) := by
    rw [← map_mul, hroot, Valuation.map_neg, map_mul]

  have hm1 : 1 ≤ max 1 (v y) := le_max_left _ _
  have hsm : v y ≤ max 1 (v y) := le_max_right _ _
  have hH : v (H.eval y) ≤
      max (v x₀ ^ q * max 1 (v y) ^ (q - 1)) (v x₀ ^ (q - 1) * v y ^ q) := by
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le hHdeg)]
    refine Valuation.map_sum_le _ fun i hi => ?_
    rw [Finset.mem_range, Nat.lt_succ_iff] at hi
    rw [map_mul, map_pow]
    rcases hi.lt_or_eq with hi | rfl
    · refine le_trans ?_ (le_max_left _ _)
      calc v (H.coeff i) * v y ^ i ≤ v x₀ ^ q * v y ^ i :=
            mul_le_mul_of_nonneg_right (hHb i hi) zero_le'
        _ ≤ v x₀ ^ q * max 1 (v y) ^ i :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ zero_le' hsm i) zero_le'
        _ ≤ v x₀ ^ q * max 1 (v y) ^ (q - 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hm1 (by omega)) zero_le'
    · exact le_trans (mul_le_mul_of_nonneg_right hHq zero_le') (le_max_right _ _)
  have hB : v (x₀ ^ q - y) * v (x₀ - y ^ q) ≤
      max (v x₀ ^ q * max 1 (v y) ^ (q - 1)) (v x₀ ^ (q - 1) * v y ^ q) := hE.trans hH
  have hvx : v (x₀ ^ q) = v x₀ ^ q := map_pow _ _ _
  have hvy : v (y ^ q) = v y ^ q := map_pow _ _ _
  have hXq1 : v x₀ ^ (q - 1) ≤ v x₀ ^ q := pow_le_pow_right₀ hX1 hq1.le
  have hXltXq : v x₀ < v x₀ ^ q := by
    conv_lhs => rw [← pow_one (v x₀)]
    exact pow_lt_pow_right₀ hx hq

  rcases lt_trichotomy (v x₀ ^ q) (v y) with h1 | h1 | h1
  ·
    exfalso
    have hs1 : 1 < v y := lt_trans (one_lt_pow₀ hx hq0) h1
    have hs0 : 0 < v y := lt_trans zero_lt_one hs1
    have hms : max 1 (v y) = v y := max_eq_right hs1.le
    have ha : v (x₀ ^ q - y) = v y :=
      Valuation.map_sub_eq_of_lt_right _ (by rw [hvx]; exact h1)
    have hXs : v x₀ < v y ^ q :=
      lt_of_lt_of_le (lt_trans hXltXq h1) (le_self_pow₀ hs1.le hq0)
    have hb : v (x₀ - y ^ q) = v y ^ q := by
      rw [Valuation.map_sub_eq_of_lt_right _ (by rw [hvy]; exact hXs), hvy]
    rw [ha, hb, hms] at hB
    refine absurd hB (not_le.mpr (max_lt ?_ ?_))
    · calc v x₀ ^ q * v y ^ (q - 1) < v y * v y ^ (q - 1) :=
            mul_lt_mul_of_pos_right h1 (pow_pos hs0 _)
        _ ≤ v y * v y ^ q :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hs1.le hq1.le) zero_le'
    · exact mul_lt_mul_of_pos_right (lt_of_le_of_lt hXq1 h1) (pow_pos hs0 _)
  ·
    left
    have hs1 : 1 < v y := by rw [← h1]; exact one_lt_pow₀ hx hq0
    have hs0 : 0 < v y := lt_trans zero_lt_one hs1
    have hms : max 1 (v y) = v y := max_eq_right hs1.le
    have hXs : v x₀ < v y ^ q :=
      lt_of_lt_of_le (by rw [← h1]; exact hXltXq) (le_self_pow₀ hs1.le hq0)
    have hb : v (x₀ - y ^ q) = v y ^ q := by
      rw [Valuation.map_sub_eq_of_lt_right _ (by rw [hvy]; exact hXs), hvy]
    refine ⟨h1.symm, ?_⟩
    rw [Valuation.map_sub_swap]
    refine le_of_mul_le_mul_right ?_ (pow_pos hs0 q)
    have hE2 := hE'
    rw [hb] at hE2
    rw [hE2, mul_assoc]
    refine mul_le_mul_of_nonneg_left (hH.trans ?_) zero_le'
    rw [hms, max_le_iff]
    refine ⟨?_, le_rfl⟩
    calc v x₀ ^ q * v y ^ (q - 1) = v y ^ q := by rw [h1, ← pow_succ', ← hqq]
      _ ≤ v x₀ ^ (q - 1) * v y ^ q := le_mul_of_one_le_left zero_le' (one_le_pow₀ hX1)
  ·
    have ha : v (x₀ ^ q - y) = v x₀ ^ q := by
      rw [Valuation.map_sub_eq_of_lt_left _ (by rw [hvx]; exact h1), hvx]
    rcases lt_trichotomy (v x₀) (v y ^ q) with h2 | h2 | h2
    ·
      exfalso
      have hs1 : 1 < v y := by
        by_contra h
        exact absurd (lt_of_lt_of_le hx (h2.le.trans (pow_le_one₀ zero_le' (not_lt.mp h))))
          (lt_irrefl _)
      have hs0 : 0 < v y := lt_trans zero_lt_one hs1
      have hms : max 1 (v y) = v y := max_eq_right hs1.le
      have hb : v (x₀ - y ^ q) = v y ^ q := by
        rw [Valuation.map_sub_eq_of_lt_right _ (by rw [hvy]; exact h2), hvy]
      rw [ha, hb, hms] at hB
      refine absurd hB (not_le.mpr (max_lt ?_ ?_))
      · exact mul_lt_mul_of_pos_left (pow_lt_pow_right₀ hs1 hq1) (pow_pos hX0 _)
      · exact mul_lt_mul_of_pos_right (pow_lt_pow_right₀ hx hq1) (pow_pos hs0 _)
    ·
      right
      have hs1 : 1 < v y := by
        by_contra h
        exact absurd (lt_of_lt_of_le hx (h2.le.trans (pow_le_one₀ zero_le' (not_lt.mp h))))
          (lt_irrefl _)
      have hs0 : 0 < v y := lt_trans zero_lt_one hs1
      have hms : max 1 (v y) = v y := max_eq_right hs1.le
      refine ⟨h2.symm, ?_⟩
      refine le_of_mul_le_mul_left ?_ (pow_pos hX0 q)
      have hE2 := hE'
      rw [ha] at hE2
      rw [hE2, mul_left_comm]
      refine mul_le_mul_of_nonneg_left (hH.trans ?_) zero_le'
      rw [hms, max_le_iff]
      refine ⟨le_rfl, ?_⟩
      calc v x₀ ^ (q - 1) * v y ^ q = v x₀ ^ q := by rw [← h2, ← pow_succ, ← hqq]
        _ ≤ v x₀ ^ q * v y ^ (q - 1) := le_mul_of_one_le_right zero_le' (one_le_pow₀ hs1.le)
    ·
      exfalso
      have hb : v (x₀ - y ^ q) = v x₀ :=
        Valuation.map_sub_eq_of_lt_left _ (by rw [hvy]; exact h2)
      rw [ha, hb] at hB
      have hmX : max 1 (v y) ^ (q - 1) < v x₀ := by
        rcases le_total (v y) 1 with hs | hs
        · rw [max_eq_left hs, one_pow]; exact hx
        · rw [max_eq_right hs]
          exact lt_of_le_of_lt (pow_le_pow_right₀ hs hq1.le) h2
      refine absurd hB (not_le.mpr (max_lt ?_ ?_))
      · exact mul_lt_mul_of_pos_left hmX (pow_pos hX0 _)
      · calc v x₀ ^ (q - 1) * v y ^ q < v x₀ ^ (q - 1) * v x₀ := mul_lt_mul_of_pos_left h2 (pow_pos hX0 _)
          _ ≤ v x₀ ^ q * v x₀ := mul_le_mul_of_nonneg_right hXq1 zero_le'

end S_Polynomial_valuation_root_dichotomy_of_kroneckerShape
end P2MW
export P2MW.S_Polynomial_valuation_root_dichotomy_of_kroneckerShape (solution)
