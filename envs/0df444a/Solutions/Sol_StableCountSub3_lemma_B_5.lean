-- Prove2me | solution 1 for StableCountSub3.lemma_B_5
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T15:35:27.232738+00:00
-- url     : https://prove2.me/submissions/d18e31dc-a147-411b-be70-aaae27cb5647

import Mathlib
import Definitions.Def_StableCountSub3_Savings

open Finset

namespace StableCountSub3.B5Aux

lemma log_eq_neg (y : ℝ) (hy : 1 ≤ y) :
    Real.log ((y+1)/y) = - Real.log (1 - 1/(y+1)) := by
  have h0 : y ≠ 0 := by positivity
  have h1 : y + 1 ≠ 0 := by positivity
  rw [← Real.log_inv, one_sub_div h1, add_sub_cancel_right, inv_div]

lemma log_up (y : ℝ) (hy : 1 ≤ y) (n : ℕ) :
    Real.log ((y+1)/y) ≤ (∑ i ∈ range n, (1/(y+1))^(i+1)/(i+1)) + (1/(y+1))^(n+1)/(1 - 1/(y+1)) := by
  have hx0 : 0 < 1/(y+1) := by positivity
  have hx1 : 1/(y+1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have habs : |1/(y+1)| < 1 := by rw [abs_of_pos hx0]; exact hx1
  have h := Real.abs_log_sub_add_sum_range_le habs n
  rw [abs_of_pos hx0] at h
  rw [log_eq_neg y hy]; have := (abs_le.mp h).1; linarith

lemma log_lo (y : ℝ) (hy : 1 ≤ y) (n : ℕ) :
    (∑ i ∈ range n, (1/(y+1))^(i+1)/(i+1)) ≤ Real.log ((y+1)/y) := by
  have hx0 : 0 < 1/(y+1) := by positivity
  have hx1 : 1/(y+1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have habs : |1/(y+1)| < 1 := by rw [abs_of_pos hx0]; exact hx1
  have h := Real.hasSum_pow_div_log_of_abs_lt_one habs
  rw [log_eq_neg y hy]; exact sum_le_hasSum (range n) (fun i _ => by positivity) h

/-- general term of `δ`. -/
noncomputable def T (y : ℝ) : ℝ := 2 * Real.log ((y+1)/y) / ((y+1)*(y+2)*(y+3))

lemma T_lo (y : ℝ) (hy : 1 ≤ y) (n : ℕ) (q : ℝ)
    (hq : q ≤ 2 * (∑ i ∈ range n, (1/(y+1))^(i+1)/(i+1)) / ((y+1)*(y+2)*(y+3))) : q ≤ T y := by
  refine hq.trans ?_
  have hD : 0 < (y+1)*(y+2)*(y+3) := mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  unfold T
  rw [div_le_div_iff_of_pos_right hD]
  linarith [log_lo y hy n]

lemma T_nonneg (y : ℝ) (hy : 1 ≤ y) : 0 ≤ T y := by
  have hD : 0 < (y+1)*(y+2)*(y+3) := mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have : 0 ≤ Real.log ((y+1)/y) := Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  unfold T; positivity

lemma T_le (y : ℝ) (hy : 1 ≤ y) : T y ≤ 2 / (y+1)^2 := by
  have hD : 0 < (y+1)*(y+2)*(y+3) := mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hl : Real.log ((y+1)/y) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (x := (y+1)/y) (by positivity)
    have h2 : (y+1)/y - 1 ≤ 1 := by
      rw [div_sub_one (by positivity), div_le_one (by linarith)]; linarith
    linarith
  have : 0 ≤ Real.log ((y+1)/y) := Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  unfold T
  rw [div_le_div_iff₀ hD (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg this (by linarith : (0:ℝ) ≤ y + 1)) (by linarith : (0:ℝ) ≤ y + 1)]

lemma delta_eq (d : ℕ) : delta d = ∑' i : ℕ, T ((i:ℝ) + d) := rfl

lemma T_summable (d : ℕ) (hd : 1 ≤ d) : Summable (fun i : ℕ => T ((i:ℝ) + d)) := by
  have hs : Summable (fun i : ℕ => 2 / ((i:ℝ) + 1)^2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    have := this.mul_left 2
    refine this.congr (fun i => ?_)
    push_cast; ring
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  refine Summable.of_nonneg_of_le (fun i => T_nonneg _ (by have := (Nat.cast_nonneg i : (0:ℝ) ≤ i); linarith)) (fun i => ?_) hs
  · refine (T_le _ (by have := (Nat.cast_nonneg i : (0:ℝ) ≤ i); linarith)).trans ?_
    gcongr; linarith
  
lemma delta_succ (d : ℕ) (hd : 1 ≤ d) : delta d = T d + delta (d+1) := by
  rw [delta_eq, (T_summable d hd).tsum_eq_zero_add, delta_eq]
  simp only [Nat.cast_zero, zero_add, Nat.cast_add, Nat.cast_one]
  congr 1; congr 1; ext i; congr 1; ring

end StableCountSub3.B5Aux

namespace StableCountSub3.B5Aux

noncomputable def U (y : ℝ) : ℝ := 2 * Real.log ((y+1)/y) / (y+2)

lemma U_nonneg (y : ℝ) (hy : 1 ≤ y) : 0 ≤ U y := by
  have : 0 ≤ Real.log ((y+1)/y) := Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  unfold U; apply div_nonneg (by linarith) (by linarith)

lemma U_le (y : ℝ) (hy : 1 ≤ y) (n : ℕ) (q : ℝ)
    (hq : (∑ i ∈ range n, (1/(y+1))^(i+1)/(i+1)) + (1/(y+1))^(n+1)/(1 - 1/(y+1)) ≤ q) :
    U y ≤ 2 * q / (y+2) := by
  unfold U
  rw [div_le_div_iff_of_pos_right (by linarith)]
  linarith [log_up y hy n]

noncomputable def f0 (i : ℕ) : ℝ := 2 * Real.log ((i : ℝ) + 1) / (((i : ℝ) + 2) * ((i : ℝ) + 3))

lemma f0_nonneg (i : ℕ) : 0 ≤ f0 i := by
  have : 0 ≤ Real.log ((i : ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)])
  unfold f0; positivity

lemma f0_ident (K : ℕ) :
    (∑ i ∈ range K, f0 i) + 2 * Real.log ((K:ℝ) + 1) / ((K:ℝ) + 2) = ∑ i ∈ range K, U ((i:ℝ) + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, sum_range_succ, ← ih]
    have hK : (0:ℝ) ≤ K := Nat.cast_nonneg K
    have h1 : (K:ℝ) + 1 + 1 ≠ 0 := by positivity
    have h2 : (K:ℝ) + 1 ≠ 0 := by positivity
    unfold f0 U
    push_cast
    rw [Real.log_div h1 h2]
    have h3 : (K:ℝ) + 2 ≠ 0 := by positivity
    have h4 : (K:ℝ) + 3 ≠ 0 := by positivity
    have h5 : (K:ℝ) + 1 + 2 ≠ 0 := by positivity
    have e1 : (K:ℝ) + 1 + 1 = K + 2 := by ring
    have e2 : (K:ℝ) + 1 + 2 = K + 3 := by ring
    rw [e1, e2]
    field_simp
    ring

/-- telescoping majorant for the tail. -/
noncomputable def GG (z : ℝ) : ℝ :=
  4 / (2*z-1) - 10 / (2*z-1)^2 + (244/9) / (2*z-1)^3 - (208/3) / (2*z-1)^4

lemma GG_nonneg (z : ℝ) (hz : 2 ≤ z) : 0 ≤ GG z := by
  have hw : 3 ≤ 2*z - 1 := by linarith
  have hw0 : 0 < 2*z - 1 := by linarith
  have e : GG z = (4*(2*z-1) - 10) / (2*z-1)^2 + ((244/9)*(2*z-1) - 208/3) / (2*z-1)^4 := by
    unfold GG; field_simp; ring
  rw [e]
  apply add_nonneg
  · apply div_nonneg (by linarith) (by positivity)
  · apply div_nonneg (by linarith) (by positivity)

lemma log_tail (y : ℝ) (hy : 2 ≤ y) :
    Real.log ((y+1)/y) ≤ 1/y - 1/(2*y^2) + 1/(3*y^3) - 1/(4*y^4) + 1/(5*y^5) + 1/(y^5*(y-1)) := by
  have hy0 : 0 < y := by linarith
  have hx : |(-1/y)| < 1 := by
    rw [abs_div, abs_neg, abs_one, abs_of_pos hy0, div_lt_one hy0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 5
  have ha : |(-1/y)| = 1/y := by rw [abs_div, abs_neg, abs_one, abs_of_pos hy0]
  rw [ha] at h
  have h2 := (abs_le.mp h).2
  have e1 : (1:ℝ) - -1/y = (y+1)/y := by field_simp; ring
  rw [e1] at h2
  have e2 : (1/y)^(5+1) / (1 - 1/y) = 1/(y^5*(y-1)) := by
    have : y - 1 ≠ 0 := by linarith
    rw [show (1:ℝ) - 1/y = (y-1)/y by field_simp, div_pow, one_pow]
    field_simp
  rw [e2] at h2
  simp only [sum_range_succ, sum_range_zero] at h2
  norm_num at h2
  have e3 : (-1/y) + (-1/y)^2/2 + (-1/y)^3/3 + (-1/y)^4/4 + (-1/y)^5/5
      = -(1/y - 1/(2*y^2) + 1/(3*y^3) - 1/(4*y^4) + 1/(5*y^5)) := by
    field_simp; ring
  have e4 : 1/(y^5*(y-1)) = (y-1)⁻¹ * (y^5)⁻¹ := by rw [one_div, mul_inv, mul_comm]
  linarith [e3, e4, h2]

lemma U_tail (k : ℕ) : U ((k:ℝ) + 20) ≤ GG ((k:ℝ) + 20) - GG ((k:ℝ) + 21) := by
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  set y : ℝ := (k:ℝ) + 20 with hydef
  have hy : 20 ≤ y := by linarith
  have hL := log_tail y (by linarith)
  have hU : U y ≤ 2 * (1/y - 1/(2*y^2) + 1/(3*y^3) - 1/(4*y^4) + 1/(5*y^5) + 1/(y^5*(y-1))) / (y+2) := by
    unfold U; rw [div_le_div_iff_of_pos_right (by linarith)]; linarith
  refine hU.trans ?_
  have e21 : (k:ℝ) + 21 = y + 1 := by rw [hydef]; ring
  rw [e21]
  have key : GG y - GG (y+1) - 2 * (1/y - 1/(2*y^2) + 1/(3*y^3) - 1/(4*y^4) + 1/(5*y^5) + 1/(y^5*(y-1))) / (y+2)
      = (46080*(k:ℝ)^10 + 8444864*k^9 + 691143776*k^8 + 33213719936*k^7 + 1035771358944*k^6
          + 21840181024524*k^5 + 314075204453166*k^4 + 3023141842798426*k^3
          + 18458746603829569*k^2 + 63450136713983479*k + 90010449169489836)
        / (90 * ((k:ℝ)+20)^5 * ((k:ℝ)+19) * ((k:ℝ)+22) * (2*(k:ℝ)+39)^4 * (2*(k:ℝ)+41)^4) := by
    rw [hydef]
    have a1 : (k:ℝ) + 20 ≠ 0 := by positivity
    have a2 : (k:ℝ) + 20 - 1 ≠ 0 := by linarith
    have a3 : (k:ℝ) + 20 + 2 ≠ 0 := by positivity
    have a4 : 2 * ((k:ℝ) + 20) - 1 ≠ 0 := by linarith
    have a5 : 2 * ((k:ℝ) + 20 + 1) - 1 ≠ 0 := by linarith
    have a6 : (k:ℝ) + 19 ≠ 0 := by positivity
    have a7 : (k:ℝ) + 22 ≠ 0 := by positivity
    have a8 : 2 * (k:ℝ) + 39 ≠ 0 := by positivity
    have a9 : 2 * (k:ℝ) + 41 ≠ 0 := by positivity
    unfold GG
    field_simp
    ring
  have : 0 ≤ (46080*(k:ℝ)^10 + 8444864*k^9 + 691143776*k^8 + 33213719936*k^7 + 1035771358944*k^6
          + 21840181024524*k^5 + 314075204453166*k^4 + 3023141842798426*k^3
          + 18458746603829569*k^2 + 63450136713983479*k + 90010449169489836)
        / (90 * ((k:ℝ)+20)^5 * ((k:ℝ)+19) * ((k:ℝ)+22) * (2*(k:ℝ)+39)^4 * (2*(k:ℝ)+41)^4) := by
    positivity
  linarith

lemma U_tail_sum (m : ℕ) :
    ∑ i ∈ range m, U ((i:ℝ) + 20) ≤ GG 20 - GG ((m:ℝ) + 20) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have h := U_tail m
    have e : ((m+1 : ℕ):ℝ) + 20 = (m:ℝ) + 21 := by push_cast; ring
    rw [e]; linarith

lemma C0_le_aux (B : ℝ) (hB : ∑ i ∈ range 19, U ((i:ℝ) + 1) ≤ B) : C0 ≤ B + GG 20 := by
  have hC : C0 = ∑' i, f0 i := rfl
  rw [hC]
  refine Real.tsum_le_of_sum_range_le f0_nonneg (fun K => ?_)
  have h1 := f0_ident K
  have hK : 0 ≤ 2 * Real.log ((K:ℝ) + 1) / ((K:ℝ) + 2) := by
    have : 0 ≤ Real.log ((K : ℝ) + 1) :=
      Real.log_nonneg (by linarith [(Nat.cast_nonneg K : (0:ℝ) ≤ K)])
    positivity
  have h2 : ∑ i ∈ range K, U ((i:ℝ) + 1) ≤ ∑ i ∈ range (19 + K), U ((i:ℝ) + 1) := by
    apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
    intro i _ _; exact U_nonneg _ (by linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)])
  rw [sum_range_add] at h2
  have h3 : ∑ i ∈ range K, U (((19 + i : ℕ) : ℝ) + 1) = ∑ i ∈ range K, U ((i:ℝ) + 20) := by
    apply sum_congr rfl; intro i _; congr 1; push_cast; ring
  rw [h3] at h2
  have h4 := U_tail_sum K
  have h5 := GG_nonneg ((K:ℝ) + 20) (by linarith [(Nat.cast_nonneg K : (0:ℝ) ≤ K)])
  linarith

lemma log_lo4 (a x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (ha : a = 2 * 2 * (1 - x)) (n : ℕ) :
    2 * 0.6931471803 - ((∑ i ∈ range n, x^(i+1)/(i+1)) + x^(n+1)/(1-x)) < Real.log a := by
  have habs : |x| < 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have h := Real.abs_log_sub_add_sum_range_le habs n
  rw [abs_of_nonneg hx0] at h
  have h2 := (abs_le.mp h).1
  rw [ha, Real.log_mul (by norm_num) (by linarith), Real.log_mul (by norm_num) (by norm_num)]
  have := Real.log_two_gt_d9
  linarith

end StableCountSub3.B5Aux

open StableCountSub3.B5Aux in
theorem solution :
    StableCountSub3.C0 < Real.log 3.332 ∧
    StableCountSub3.C0 - 2 / 3 * (StableCountSub3.delta 1 + 2 * StableCountSub3.delta 2) < Real.log 3.060 ∧
    StableCountSub3.C0 - 2 / 3 * (StableCountSub3.delta 1 + 2 * StableCountSub3.delta 2)
      - 4 * StableCountSub3.delta 4 < Real.log 2.999 := by
  -- upper bound for C0
  have hU1 := U_le 1 (by norm_num) 30 0.693147181463 (by norm_num [Finset.sum_range_succ])
  have hU2 := U_le 2 (by norm_num) 19 0.405465108518 (by norm_num [Finset.sum_range_succ])
  have hU3 := U_le 3 (by norm_num) 15 0.287682072744 (by norm_num [Finset.sum_range_succ])
  have hU4 := U_le 4 (by norm_num) 13 0.223143551505 (by norm_num [Finset.sum_range_succ])
  have hU5 := U_le 5 (by norm_num) 11 0.182321557300 (by norm_num [Finset.sum_range_succ])
  have hU6 := U_le 6 (by norm_num) 10 0.154150680365 (by norm_num [Finset.sum_range_succ])
  have hU7 := U_le 7 (by norm_num) 10 0.133531392746 (by norm_num [Finset.sum_range_succ])
  have hU8 := U_le 8 (by norm_num) 9 0.117783035948 (by norm_num [Finset.sum_range_succ])
  have hU9 := U_le 9 (by norm_num) 9 0.105360515758 (by norm_num [Finset.sum_range_succ])
  have hU10 := U_le 10 (by norm_num) 8 0.095310180220 (by norm_num [Finset.sum_range_succ])
  have hU11 := U_le 11 (by norm_num) 8 0.087011377178 (by norm_num [Finset.sum_range_succ])
  have hU12 := U_le 12 (by norm_num) 8 0.080042707765 (by norm_num [Finset.sum_range_succ])
  have hU13 := U_le 13 (by norm_num) 7 0.074107972794 (by norm_num [Finset.sum_range_succ])
  have hU14 := U_le 14 (by norm_num) 7 0.068992871854 (by norm_num [Finset.sum_range_succ])
  have hU15 := U_le 15 (by norm_num) 7 0.064538521356 (by norm_num [Finset.sum_range_succ])
  have hU16 := U_le 16 (by norm_num) 7 0.060624621950 (by norm_num [Finset.sum_range_succ])
  have hU17 := U_le 17 (by norm_num) 7 0.057158413925 (by norm_num [Finset.sum_range_succ])
  have hU18 := U_le 18 (by norm_num) 7 0.054067221325 (by norm_num [Finset.sum_range_succ])
  have hU19 := U_le 19 (by norm_num) 6 0.051293295094 (by norm_num [Finset.sum_range_succ])
  have hT1 := T_lo 1 (by norm_num) 34 0.057762265046 (by norm_num [Finset.sum_range_succ])
  have hT2 := T_lo 2 (by norm_num) 21 0.013515503603 (by norm_num [Finset.sum_range_succ])
  have hT3 := T_lo 3 (by norm_num) 16 0.004794701207 (by norm_num [Finset.sum_range_succ])
  have hT4 := T_lo 4 (by norm_num) 14 0.002125176679 (by norm_num [Finset.sum_range_succ])
  have hT5 := T_lo 5 (by norm_num) 12 0.001085247361 (by norm_num [Finset.sum_range_succ])
  have hT6 := T_lo 6 (by norm_num) 11 0.000611709046 (by norm_num [Finset.sum_range_succ])
  have hT7 := T_lo 7 (by norm_num) 11 0.000370920535 (by norm_num [Finset.sum_range_succ])
  have hT8 := T_lo 8 (by norm_num) 10 0.000237945526 (by norm_num [Finset.sum_range_succ])
  have hT9 := T_lo 9 (by norm_num) 10 0.000159637144 (by norm_num [Finset.sum_range_succ])
  have hT10 := T_lo 10 (by norm_num) 9 0.000111084125 (by norm_num [Finset.sum_range_succ])
  have hT11 := T_lo 11 (by norm_num) 9 0.000079680748 (by norm_num [Finset.sum_range_succ])
  have hT12 := T_lo 12 (by norm_num) 9 0.000058639346 (by norm_num [Finset.sum_range_succ])
  have hT13 := T_lo 13 (by norm_num) 8 0.000044111888 (by norm_num [Finset.sum_range_succ])
  have hT14 := T_lo 14 (by norm_num) 8 0.000033820035 (by norm_num [Finset.sum_range_succ])
  have hT15 := T_lo 15 (by norm_num) 8 0.000026363774 (by norm_num [Finset.sum_range_succ])
  have hT16 := T_lo 16 (by norm_num) 8 0.000020854703 (by norm_num [Finset.sum_range_succ])
  have hT17 := T_lo 17 (by norm_num) 7 0.000016712986 (by norm_num [Finset.sum_range_succ])
  have hT18 := T_lo 18 (by norm_num) 7 0.000013550682 (by norm_num [Finset.sum_range_succ])
  have hT19 := T_lo 19 (by norm_num) 7 0.000011102444 (by norm_num [Finset.sum_range_succ])
  have hT20 := T_lo 20 (by norm_num) 7 0.000009183166 (by norm_num [Finset.sum_range_succ])
  have hT21 := T_lo 21 (by norm_num) 7 0.000007661399 (by norm_num [Finset.sum_range_succ])
  have hT22 := T_lo 22 (by norm_num) 7 0.000006442284 (by norm_num [Finset.sum_range_succ])
  have hT23 := T_lo 23 (by norm_num) 7 0.000005456360 (by norm_num [Finset.sum_range_succ])
  have hT24 := T_lo 24 (by norm_num) 7 0.000004652079 (by norm_num [Finset.sum_range_succ])
  have hT25 := T_lo 25 (by norm_num) 7 0.000003990711 (by norm_num [Finset.sum_range_succ])
  have hT26 := T_lo 26 (by norm_num) 6 0.000003442832 (by norm_num [Finset.sum_range_succ])
  have hT27 := T_lo 27 (by norm_num) 6 0.000002985849 (by norm_num [Finset.sum_range_succ])
  have hT28 := T_lo 28 (by norm_num) 6 0.000002602248 (by norm_num [Finset.sum_range_succ])
  have hT29 := T_lo 29 (by norm_num) 6 0.000002278330 (by norm_num [Finset.sum_range_succ])
  have hT30 := T_lo 30 (by norm_num) 6 0.000002003288 (by norm_num [Finset.sum_range_succ])
  have hT31 := T_lo 31 (by norm_num) 6 0.000001768532 (by norm_num [Finset.sum_range_succ])
  have hT32 := T_lo 32 (by norm_num) 6 0.000001567184 (by norm_num [Finset.sum_range_succ])
  have hT33 := T_lo 33 (by norm_num) 6 0.000001393695 (by norm_num [Finset.sum_range_succ])
  have hT34 := T_lo 34 (by norm_num) 6 0.000001243566 (by norm_num [Finset.sum_range_succ])
  have hT35 := T_lo 35 (by norm_num) 6 0.000001113121 (by norm_num [Finset.sum_range_succ])
  have hT36 := T_lo 36 (by norm_num) 6 0.000000999342 (by norm_num [Finset.sum_range_succ])
  have hT37 := T_lo 37 (by norm_num) 6 0.000000899738 (by norm_num [Finset.sum_range_succ])
  have hT38 := T_lo 38 (by norm_num) 6 0.000000812241 (by norm_num [Finset.sum_range_succ])
  have hT39 := T_lo 39 (by norm_num) 6 0.000000735127 (by norm_num [Finset.sum_range_succ])
  have hS : ∑ i ∈ range 19, U ((i:ℝ) + 1) ≤ 1.107149488850 := by
    simp only [sum_range_succ, sum_range_zero]
    norm_num
    linarith [hU1, hU2, hU3, hU4, hU5, hU6, hU7, hU8, hU9, hU10, hU11, hU12, hU13, hU14, hU15,
      hU16, hU17, hU18, hU19]
  have hC0 := C0_le_aux _ hS
  have hGG : GG 20 = 17158/177957 := by unfold GG; norm_num
  -- lower bounds for the deltas
  have hd1 := delta_succ 1 le_rfl
  have hd2 := delta_succ 2 (by norm_num)
  have hd3 := delta_succ 3 (by norm_num)
  norm_num at hd1 hd2 hd3
  have hd4 : ∑ i ∈ range 36, T ((i:ℝ) + 4) ≤ StableCountSub3.delta 4 := by
    have := sum_le_hasSum (range 36)
      (fun i _ => T_nonneg ((i:ℝ) + (4:ℕ)) (by push_cast; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]))
      (T_summable 4 (by norm_num)).hasSum
    rw [delta_eq]; exact this
  simp only [sum_range_succ, sum_range_zero] at hd4
  norm_num at hd4
  have l1 := log_lo4 3.332 0.167 (by norm_num) (by norm_num) (by norm_num) 14
  have l2 := log_lo4 3.060 0.235 (by norm_num) (by norm_num) (by norm_num) 14
  have l3 := log_lo4 2.999 0.25025 (by norm_num) (by norm_num) (by norm_num) 14
  simp only [sum_range_succ, sum_range_zero] at l1 l2 l3
  norm_num at l1 l2 l3
  refine ⟨by linarith, by linarith, by linarith⟩
