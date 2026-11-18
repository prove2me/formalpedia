-- Prove2me | solution 1 for StochGradTrack.Dimin.sum_bounds
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:15:37.315355+00:00
-- url     : https://prove2.me/submissions/5f0beb5b-9366-48c8-b85c-28e6b239e362

import Mathlib
namespace StochGradTrack.Dimin

lemma aux_mul (x c p : ℝ) (hx : 0 < x) (hc : 0 ≤ x + c) :
    x ^ p * (1 + c / x) ^ p = (x + c) ^ p := by
  rw [← Real.mul_rpow hx.le (by
    have : 1 + c / x = (x + c) / x := by field_simp
    rw [this]; positivity)]
  congr 1
  field_simp

lemma aux_pow (x p : ℝ) (hx : 0 < x) : x ^ p * (1 / x) = x ^ (p - 1) := by
  rw [Real.rpow_sub_one hx.ne']; ring

lemma lemA (x p : ℝ) (hx : 0 < x) (hp : 1 ≤ p) :
    x ^ p + p * x ^ (p - 1) ≤ (x + 1) ^ p := by
  have hb := one_add_mul_self_le_rpow_one_add (s := 1 / x) (by
    have : 0 ≤ 1 / x := by positivity
    linarith) hp
  have hxp : 0 ≤ x ^ p := Real.rpow_nonneg hx.le p
  have h := mul_le_mul_of_nonneg_left hb hxp
  rw [aux_mul x 1 p hx (by linarith)] at h
  have e : x ^ p * (1 + p * (1 / x)) = x ^ p + p * x ^ (p - 1) := by
    rw [← aux_pow x p hx]; ring
  linarith

lemma lemB (x p : ℝ) (hx : 1 ≤ x) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (x - 1) ^ p ≤ x ^ p - p * x ^ (p - 1) := by
  have hx0 : 0 < x := by linarith
  have hb := rpow_one_add_le_one_add_mul_self (s := -1 / x) (by
    rw [neg_div, neg_le_neg_iff, div_le_one hx0]; exact hx) hp0 hp1
  have hxp : 0 ≤ x ^ p := Real.rpow_nonneg hx0.le p
  have h := mul_le_mul_of_nonneg_left hb hxp
  rw [aux_mul x (-1) p hx0 (by linarith)] at h
  have e : x ^ p * (1 + p * (-1 / x)) = x ^ p - p * x ^ (p - 1) := by
    rw [← aux_pow x p hx0]; ring
  rw [sub_eq_add_neg]; linarith

lemma lemC (x p : ℝ) (hx : 1 < x) (hp0 : p ≤ 0) (hp1 : -1 ≤ p) :
    x ^ p - p * x ^ (p - 1) ≤ (x - 1) ^ p := by
  have hx0 : 0 < x := by linarith
  have hs : -1 ≤ -1 / x := by
    rw [neg_div, neg_le_neg_iff, div_le_one hx0]; exact hx.le
  have hb := rpow_one_add_le_one_add_mul_self (s := -1 / x) hs (p := -p) (by linarith) (by linarith)
  have hbase : 0 < 1 + -1 / x := by
    have : 1 / x < 1 := by rw [div_lt_one hx0]; exact hx
    rw [neg_div]; linarith
  have hq : 0 < 1 + -p * (-1 / x) := by
    have : 0 ≤ 1 / x := by positivity
    have : 1 / x < 1 := by rw [div_lt_one hx0]; exact hx
    have : -p * (-1 / x) = p * (1 / x) := by ring
    nlinarith
  have hpos : 0 < (1 + -1 / x) ^ (-p) := Real.rpow_pos_of_pos hbase _
  have hinv : (1 + -p * (-1 / x))⁻¹ ≤ ((1 + -1 / x) ^ (-p))⁻¹ := by
    rw [inv_le_inv₀ hq hpos]; exact hb
  rw [Real.rpow_neg hbase.le, inv_inv] at hinv
  have hge : 1 + -p * (1 / x) ≤ (1 + -p * (-1 / x))⁻¹ := by
    rw [le_inv_comm₀ (by
      have : 0 ≤ 1 / x := by positivity
      nlinarith) hq] <;> try exact hq
    have : (1 + -p * (1 / x)) * (1 + -p * (-1 / x)) ≤ 1 := by
      have : (1 + -p * (1 / x)) * (1 + -p * (-1 / x)) = 1 - (p * (1 / x)) ^ 2 := by ring
      nlinarith [sq_nonneg (p * (1 / x))]
    have h1 : 0 < 1 + -p * (1 / x) := by
      have : 0 ≤ 1 / x := by positivity
      nlinarith
    rw [inv_eq_one_div, le_div_iff₀ h1]; linarith
  have hfin : 1 + -p * (1 / x) ≤ (1 + -1 / x) ^ p := le_trans hge (by simpa [Real.rpow_neg hbase.le] using hinv)
  have hxp : 0 ≤ x ^ p := Real.rpow_nonneg hx0.le p
  have h := mul_le_mul_of_nonneg_left hfin hxp
  rw [aux_mul x (-1) p hx0 (by linarith)] at h
  have e : x ^ p * (1 + -p * (1 / x)) = x ^ p - p * x ^ (p - 1) := by
    rw [← aux_pow x p hx0]; ring
  rw [← sub_eq_add_neg] at h; linarith


lemma sumPos1 (m p : ℝ) (hm : 0 < m) (hp : 1 ≤ p) (k : ℕ) :
    p * ∑ t ∈ Finset.range k, (m + t) ^ (p - 1) ≤ (m + k) ^ p - m ^ p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add]
    have h := lemA (m + k) p (by positivity) hp
    have e : m + ((k + 1 : ℕ) : ℝ) = m + k + 1 := by push_cast; ring
    rw [e]; linarith

lemma sumPos2 (m p : ℝ) (hm : 1 < m) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    p * ∑ t ∈ Finset.range k, (m + t) ^ (p - 1) ≤ (m + k - 1) ^ p - (m - 1) ^ p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add]
    have hk0 : (0:ℝ) ≤ k := by positivity
    have h := lemB (m + k) p (by linarith) hp0 hp1
    have e : m + ((k + 1 : ℕ) : ℝ) - 1 = m + k := by push_cast; ring
    rw [e]; linarith

lemma sumNeg (m p : ℝ) (hm : 1 < m) (hp0 : p ≤ 0) (hp1 : -1 ≤ p) (k : ℕ) :
    (-p) * ∑ t ∈ Finset.range k, (m + t) ^ (p - 1) ≤ (m - 1) ^ p - (m + k - 1) ^ p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add]
    have hk0 : (0:ℝ) ≤ k := by positivity
    have h := lemC (m + k) p (by linarith) hp0 hp1
    have e : m + ((k + 1 : ℕ) : ℝ) - 1 = m + k := by push_cast; ring
    rw [e]; linarith

lemma sumG (m p : ℝ) (hm : 1 < m) (hp : 0 < p) (k : ℕ) :
    ∑ t ∈ Finset.range k, (m + t) ^ (p - 1) ≤ 1 / p * (m + k) ^ p := by
  have hk : (0:ℝ) ≤ k := by positivity
  have key : p * ∑ t ∈ Finset.range k, (m + t) ^ (p - 1) ≤ (m + k) ^ p := by
    rcases le_total 1 p with h1 | h1
    · have := sumPos1 m p (by linarith) h1 k
      have : 0 ≤ m ^ p := Real.rpow_nonneg (by linarith) p
      linarith
    · have := sumPos2 m p hm hp.le h1 k
      have : 0 ≤ (m - 1) ^ p := Real.rpow_nonneg (by linarith) p
      have : (m + k - 1) ^ p ≤ (m + k) ^ p :=
        Real.rpow_le_rpow (by linarith) (by linarith) hp.le
      linarith
  rw [one_div_mul_eq_div, le_div_iff₀ hp]; linarith

theorem sum_bounds (θ μ m : ℝ) (hm : 1 < m) (hθμ : 1 < θ * μ) (k : ℕ) :
    (θ * μ ≠ 2 →
      ∑ t ∈ Finset.range k, (m + t) ^ (θ * μ - 3)
        ≤ max (1 / (θ * μ - 2) * (m + k) ^ (θ * μ - 2)) (1 / (2 - θ * μ) * (m - 1) ^ (θ * μ - 2))) ∧
    ∑ t ∈ Finset.range k, (m + t) ^ (θ * μ - 2) ≤ 1 / (θ * μ - 1) * (m + k) ^ (θ * μ - 1) := by
  refine ⟨fun hne => ?_, ?_⟩
  · rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h := sumNeg m (θ * μ - 2) hm (by linarith) (by linarith) k
      rw [show θ * μ - 2 - 1 = θ * μ - 3 by ring] at h
      have : 0 ≤ (m + k - 1) ^ (θ * μ - 2) := Real.rpow_nonneg (by
        have : (0:ℝ) ≤ k := by positivity
        linarith) _
      refine le_trans ?_ (le_max_right _ _)
      rw [one_div_mul_eq_div, le_div_iff₀ (by linarith)]
      have e : -(θ * μ - 2) = 2 - θ * μ := by ring
      rw [e] at h; linarith
    · have h := sumG m (θ * μ - 2) hm (by linarith) k
      rw [show θ * μ - 2 - 1 = θ * μ - 3 by ring] at h
      exact le_trans h (le_max_left _ _)
  · have h := sumG m (θ * μ - 1) hm (by linarith) k
    rw [show θ * μ - 1 - 1 = θ * μ - 2 by ring] at h
    exact h

end StochGradTrack.Dimin

theorem solution (θ μ m : ℝ) (hm : 1 < m) (hθμ : 1 < θ * μ) (k : ℕ) :
    (θ * μ ≠ 2 →
      ∑ t ∈ Finset.range k, (m + t) ^ (θ * μ - 3)
        ≤ max (1 / (θ * μ - 2) * (m + k) ^ (θ * μ - 2)) (1 / (2 - θ * μ) * (m - 1) ^ (θ * μ - 2))) ∧
    ∑ t ∈ Finset.range k, (m + t) ^ (θ * μ - 2) ≤ 1 / (θ * μ - 1) * (m + k) ^ (θ * μ - 1) :=
  StochGradTrack.Dimin.sum_bounds θ μ m hm hθμ k
