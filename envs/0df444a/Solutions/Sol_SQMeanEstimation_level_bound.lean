-- Prove2me | solution 1 for SQMeanEstimation.level_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:17:16.917183+00:00
-- url     : https://prove2.me/submissions/5a70a507-e381-4cf3-97df-139d5dce31ba

import Mathlib
import Definitions.Def_SQMeanEstimation_lqNorm
import Definitions.Def_SQMeanEstimation_vstatTol
import Definitions.Def_SQMeanEstimation_zeroSmall
import Definitions.Def_SQMeanEstimation_lowPart
import Definitions.Def_SQMeanEstimation_highPart

namespace Aux_SQMeanEstimation_level_bound

open SQMeanEstimation

theorem coord (q n x y : ℝ) (hq1 : 1 < q) (hn : 0 < n) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy : |y - x| ≤ max (1 / n) (Real.sqrt (x * (1 - x) / n))) :
    |x - (if 2 / n ≤ |y| then y else 0)| ^ q ≤
      |(if x < 4 / n then x else 0)| ^ q +
        n ^ (-q / 2) * |(if 1 / n ≤ x then x else 0)| ^ (q / 2) := by
  have ha : 0 < 1 / n := by positivity
  have h2 : 2 / n = 2 * (1 / n) := by ring
  have h4 : 4 / n = 4 * (1 / n) := by ring
  have hxn : x / n = x * (1 / n) := by ring
  obtain ⟨S, hS⟩ : ∃ S, S = Real.sqrt (x / n) := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact Real.sqrt_nonneg _
  have hS2 : S ^ 2 = x * (1 / n) := by
    rw [hS, Real.sq_sqrt (show (0 : ℝ) ≤ x / n by positivity), hxn]
  have hsq : Real.sqrt (x * (1 - x) / n) ≤ S := by
    rw [hS]
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ hn.le
    nlinarith
  have hy' : |y - x| ≤ max (1 / n) S := le_trans hy (max_le_max le_rfl hsq)
  have hnonneg1 : ∀ z : ℝ, 0 ≤ |z| ^ q := fun z => Real.rpow_nonneg (abs_nonneg z) q
  have hnonneg2 : ∀ z : ℝ, 0 ≤ n ^ (-q / 2) * |z| ^ (q / 2) :=
    fun z => mul_nonneg (Real.rpow_nonneg hn.le _) (Real.rpow_nonneg (abs_nonneg z) _)
  by_cases hyb : 2 / n ≤ |y|
  · rw [if_pos hyb]
    by_cases hx : 1 / n ≤ x
    · rw [if_pos hx, abs_of_nonneg hx0]
      have h1S : 1 / n ≤ S := by
        rw [hS]
        apply Real.le_sqrt_of_sq_le
        rw [hxn]
        nlinarith [mul_le_mul_of_nonneg_right hx ha.le]
      have hyS : |x - y| ≤ S := by
        rw [abs_sub_comm]
        exact le_trans hy' (max_le h1S le_rfl)
      have hpow : |x - y| ^ q ≤ S ^ q := Real.rpow_le_rpow (abs_nonneg _) hyS (by linarith)
      have hSq : S ^ q = n ^ (-q / 2) * x ^ (q / 2) := by
        rw [hS, Real.sqrt_eq_rpow, ← Real.rpow_mul (show (0 : ℝ) ≤ x / n by positivity),
          Real.div_rpow hx0 hn.le, show -q / 2 = -(q / 2) by ring, Real.rpow_neg hn.le,
          show 1 / (2 : ℝ) * q = q / 2 by ring]
        ring
      have := hnonneg1 (if x < 4 / n then x else 0)
      linarith
    · exfalso
      push_neg at hx
      have hSlt : S < 1 / n := by
        rw [hS, Real.sqrt_lt' ha, hxn]
        nlinarith [mul_lt_mul_of_pos_right hx ha]
      have hyx : |y - x| ≤ 1 / n := le_trans hy' (max_le le_rfl hSlt.le)
      have htri : |y| ≤ |y - x| + |x| := by
        have := abs_add_le (y - x) x
        simpa using this
      rw [abs_of_nonneg hx0] at htri
      linarith
  · rw [if_neg hyb, sub_zero]
    push_neg at hyb
    by_cases hx4 : x < 4 / n
    · rw [if_pos hx4]
      have := hnonneg2 (if 1 / n ≤ x then x else 0)
      linarith
    · exfalso
      push_neg at hx4
      have hyx : x - 2 / n < |y - x| := by
        have e1 : y ≤ |y| := le_abs_self y
        have e2 : x - y ≤ |y - x| := by
          rw [abs_sub_comm]
          exact le_abs_self _
        linarith
      rcases le_max_iff.mp hy' with h | h
      · linarith
      · have hxS : x / 2 < S := by linarith
        have hx2 : 0 ≤ x / 2 := by linarith
        have hm := mul_self_lt_mul_self hx2 hxS
        have hS2' : S * S = x * (1 / n) := by rw [← hS2]; ring
        nlinarith [mul_le_mul_of_nonneg_left hx4 hx0]

theorem p1 {d : ℕ} (q n : ℝ) (hq1 : 1 < q) (hn : 0 < n)
    (u v' : Fin d → ℝ) (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1)
    (hv' : ∀ i, |v' i - u i| ≤ vstatTol n (u i)) :
    ∑ i, |u i - zeroSmall n v' i| ^ q ≤
      ∑ i, |lowPart n u i| ^ q + n ^ (-q / 2) * ∑ i, |highPart n u i| ^ (q / 2) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hvi := hv' i
  unfold vstatTol at hvi
  unfold zeroSmall lowPart highPart
  exact coord q n (u i) (v' i) hq1 hn (hu0 i) (hu1 i) hvi

theorem low_bound {d : ℕ} (q n : ℝ) (hq1 : 1 < q) (hn : 0 < n) (j : ℕ)
    (u : Fin d → ℝ) (hu0 : ∀ i, 0 ≤ u i)
    (hsum : ∑ i, u i ≤ (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1)) :
    ∑ i, |lowPart n u i| ^ q ≤ n ^ (1 - q) * (2 : ℝ) ^ (((j : ℝ) + 3) * q - 3) := by
  have hc : 0 ≤ (4 / n) ^ (q - 1) := Real.rpow_nonneg (by positivity) _
  have hpt : ∀ i, |lowPart n u i| ^ q ≤ (4 / n) ^ (q - 1) * u i := by
    intro i
    simp only [lowPart]
    split_ifs with h
    · rw [abs_of_nonneg (hu0 i)]
      rcases (hu0 i).eq_or_lt with h0 | h0
      · rw [← h0, Real.zero_rpow (by linarith)]
        simp
      · have e : u i ^ q = u i ^ (q - 1) * u i := by
          conv_lhs => rw [show q = (q - 1) + 1 by ring]
          rw [Real.rpow_add h0, Real.rpow_one]
        rw [e]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (hu0 i) h.le (by linarith)) (hu0 i)
    · rw [abs_zero, Real.zero_rpow (by linarith)]
      exact mul_nonneg hc (hu0 i)
  have h4 : (4 : ℝ) ^ (q - 1) = (2 : ℝ) ^ (2 * (q - 1)) := by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two]
    norm_num
  calc ∑ i, |lowPart n u i| ^ q ≤ ∑ i, (4 / n) ^ (q - 1) * u i :=
        Finset.sum_le_sum (fun i _ => hpt i)
    _ = (4 / n) ^ (q - 1) * ∑ i, u i := by rw [Finset.mul_sum]
    _ ≤ (4 / n) ^ (q - 1) * (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1) :=
        mul_le_mul_of_nonneg_left hsum hc
    _ = n ^ (1 - q) * (2 : ℝ) ^ (((j : ℝ) + 3) * q - 3) := by
        rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 4) hn.le, h4,
          show (1 : ℝ) - q = -(q - 1) by ring, Real.rpow_neg hn.le,
          show ((j : ℝ) + 3) * q - 3 = 2 * (q - 1) + (((j : ℝ) + 1) * q - 1) by ring,
          Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        ring

theorem high_bound {d : ℕ} (q n : ℝ) (hq1 : 1 < q) (hq2 : q < 2) (hn : 0 < n) (j : ℕ)
    (u : Fin d → ℝ) (hu0 : ∀ i, 0 ≤ u i)
    (hsum : ∑ i, u i ≤ (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1)) :
    n ^ (-q / 2) * ∑ i, |highPart n u i| ^ (q / 2)
      ≤ n ^ (1 - q) * (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1) := by
  have hpt : ∀ i, |highPart n u i| ^ (q / 2) ≤ n ^ (1 - q / 2) * u i := by
    intro i
    simp only [highPart]
    split_ifs with h
    · rw [abs_of_nonneg (hu0 i)]
      have hpos : 0 < u i := lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / n) h
      have e : u i ^ (q / 2) = u i ^ (q / 2 - 1) * u i := by
        conv_lhs => rw [show q / 2 = (q / 2 - 1) + 1 by ring]
        rw [Real.rpow_add hpos, Real.rpow_one]
      have hb : u i ^ (q / 2 - 1) ≤ (1 / n) ^ (q / 2 - 1) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h (by linarith)
      have hn' : (1 / n) ^ (q / 2 - 1) = n ^ (1 - q / 2) := by
        rw [one_div, Real.inv_rpow hn.le, ← Real.rpow_neg hn.le]
        congr 1
        ring
      rw [e, ← hn']
      exact mul_le_mul_of_nonneg_right hb (hu0 i)
    · rw [abs_zero, Real.zero_rpow (by linarith)]
      exact mul_nonneg (Real.rpow_nonneg hn.le _) (hu0 i)
  have hS : ∑ i, |highPart n u i| ^ (q / 2) ≤ n ^ (1 - q / 2) * ∑ i, u i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hpt i)
  calc n ^ (-q / 2) * ∑ i, |highPart n u i| ^ (q / 2)
      ≤ n ^ (-q / 2) * (n ^ (1 - q / 2) * ∑ i, u i) :=
        mul_le_mul_of_nonneg_left hS (Real.rpow_nonneg hn.le _)
    _ = n ^ (1 - q) * ∑ i, u i := by
        rw [← mul_assoc, ← Real.rpow_add hn, show -q / 2 + (1 - q / 2) = 1 - q by ring]
    _ ≤ n ^ (1 - q) * (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1) :=
        mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hn.le _)

theorem final_bound (q n : ℝ) (hq1 : 1 < q) (hn : 0 < n) (j : ℕ) :
    n ^ (1 - q) * ((2 : ℝ) ^ (((j : ℝ) + 3) * q - 3) + (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1)) ≤
      n ^ (1 - q) * (2 : ℝ) ^ (((j : ℝ) + 3) * q) := by
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hn.le _)
  have a1 : (2 : ℝ) ^ (((j : ℝ) + 3) * q - 3) ≤ (2 : ℝ) ^ (((j : ℝ) + 3) * q - 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hexp : ((j : ℝ) + 1) * q - 1 ≤ ((j : ℝ) + 3) * q - 1 := by nlinarith
  have a2 : (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1) ≤ (2 : ℝ) ^ (((j : ℝ) + 3) * q - 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have a3 : 2 * (2 : ℝ) ^ (((j : ℝ) + 3) * q - 1) = (2 : ℝ) ^ (((j : ℝ) + 3) * q) := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    ring
  linarith

end Aux_SQMeanEstimation_level_bound

open SQMeanEstimation Aux_SQMeanEstimation_level_bound in
theorem solution {d : ℕ} (q n : ℝ) (hq1 : 1 < q) (hq2 : q < 2) (hn : 0 < n) (j : ℕ)
    (u v' : Fin d → ℝ) (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1)
    (hsum : ∑ i, u i ≤ (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1))
    (hv' : ∀ i, |v' i - u i| ≤ vstatTol n (u i)) :
    (∑ i, |u i - zeroSmall n v' i| ^ q ≤
        ∑ i, |lowPart n u i| ^ q + n ^ (-q / 2) * ∑ i, |highPart n u i| ^ (q / 2) ∧
      ∑ i, |lowPart n u i| ^ q + n ^ (-q / 2) * ∑ i, |highPart n u i| ^ (q / 2) ≤
        n ^ (1 - q) * ((2 : ℝ) ^ (((j : ℝ) + 3) * q - 3) + (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1)) ∧
      n ^ (1 - q) * ((2 : ℝ) ^ (((j : ℝ) + 3) * q - 3) + (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1)) ≤
        n ^ (1 - q) * (2 : ℝ) ^ (((j : ℝ) + 3) * q)) ∧
    (∀ mbar : Fin d → ℝ, u = (2 : ℝ) ^ j • mbar →
      lqNorm q (mbar - (2 : ℝ) ^ (-(j : ℤ)) • zeroSmall n v') =
          (2 : ℝ) ^ (-(j : ℤ)) * lqNorm q (u - zeroSmall n v') ∧
        (2 : ℝ) ^ (-(j : ℤ)) * lqNorm q (u - zeroSmall n v') ≤ 2 ^ 3 * n ^ (1 / q - 1)) ∧
    (∀ ε' : ℝ, 0 < ε' → n = (ε' / 8) ^ (-(q / (q - 1))) → 2 ^ 3 * n ^ (1 / q - 1) = ε')
    := by
  have hq0 : q ≠ 0 := by linarith
  have hP1 := p1 q n hq1 hn u v' hu0 hu1 hv'
  have hlow := low_bound q n hq1 hn j u hu0 hsum
  have hhigh := high_bound q n hq1 hq2 hn j u hu0 hsum
  have hP2 : ∑ i, |lowPart n u i| ^ q + n ^ (-q / 2) * ∑ i, |highPart n u i| ^ (q / 2) ≤
      n ^ (1 - q) * ((2 : ℝ) ^ (((j : ℝ) + 3) * q - 3) + (2 : ℝ) ^ (((j : ℝ) + 1) * q - 1)) := by
    rw [mul_add]
    linarith
  have hP3 := final_bound q n hq1 hn j
  refine ⟨⟨hP1, hP2, hP3⟩, ?_, ?_⟩
  · intro mbar hm
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (2 : ℝ) ^ (-(j : ℤ)) := ⟨_, rfl⟩
    rw [← hc]
    have hcpos : 0 < c := by rw [hc]; exact zpow_pos (by norm_num) _
    have hc2 : c * (2 : ℝ) ^ j = 1 := by
      rw [hc, zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity)]
    have hmb : mbar - c • zeroSmall n v' = c • (u - zeroSmall n v') := by
      funext i
      have := congrFun hm i
      simp only [Pi.smul_apply, smul_eq_mul] at this
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [this, mul_sub, ← mul_assoc, hc2, one_mul]
    have hscale : ∀ x : Fin d → ℝ, lqNorm q (c • x) = c * lqNorm q x := by
      intro x
      unfold lqNorm
      have hsx : ∑ i, |(c • x) i| ^ q = c ^ q * ∑ i, |x i| ^ q := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hcpos,
          Real.mul_rpow hcpos.le (abs_nonneg _)]
      rw [hsx, Real.mul_rpow (Real.rpow_nonneg hcpos.le _)
          (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)),
        ← Real.rpow_mul hcpos.le, mul_one_div_cancel hq0, Real.rpow_one]
    refine ⟨by rw [hmb, hscale], ?_⟩
    unfold lqNorm
    have hS : ∑ i, |(u - zeroSmall n v') i| ^ q
        ≤ n ^ (1 - q) * (2 : ℝ) ^ (((j : ℝ) + 3) * q) := by
      simp only [Pi.sub_apply]
      linarith
    have hmono : (∑ i, |(u - zeroSmall n v') i| ^ q) ^ (1 / q)
        ≤ (n ^ (1 - q) * (2 : ℝ) ^ (((j : ℝ) + 3) * q)) ^ (1 / q) :=
      Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)) hS
        (by positivity)
    have h8 : (2 : ℝ) ^ (3 : ℝ) = 2 ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hval : c * (n ^ (1 - q) * (2 : ℝ) ^ (((j : ℝ) + 3) * q)) ^ (1 / q)
        = 2 ^ 3 * n ^ (1 / q - 1) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hn.le _) (Real.rpow_nonneg (by norm_num) _),
        ← Real.rpow_mul hn.le, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        show (1 - q) * (1 / q) = 1 / q - 1 by rw [sub_mul, one_mul, mul_one_div_cancel hq0],
        show ((j : ℝ) + 3) * q * (1 / q) = (j : ℝ) + 3 by
          rw [mul_assoc, mul_one_div_cancel hq0, mul_one],
        Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast 2 j, h8]
      calc c * (n ^ (1 / q - 1) * ((2 : ℝ) ^ j * 2 ^ 3))
          = (c * (2 : ℝ) ^ j) * (2 ^ 3 * n ^ (1 / q - 1)) := by ring
        _ = 2 ^ 3 * n ^ (1 / q - 1) := by rw [hc2, one_mul]
    calc c * (∑ i, |(u - zeroSmall n v') i| ^ q) ^ (1 / q)
        ≤ c * (n ^ (1 - q) * (2 : ℝ) ^ (((j : ℝ) + 3) * q)) ^ (1 / q) :=
          mul_le_mul_of_nonneg_left hmono hcpos.le
      _ = 2 ^ 3 * n ^ (1 / q - 1) := hval
  · intro ε' hε hneq
    have hq1' : q - 1 ≠ 0 := by linarith
    have key : -(q / (q - 1)) * (1 / q - 1) = 1 := by
      first
        | (field_simp; ring1)
        | field_simp
    rw [hneq, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ ε' / 8), key, Real.rpow_one]
    ring
