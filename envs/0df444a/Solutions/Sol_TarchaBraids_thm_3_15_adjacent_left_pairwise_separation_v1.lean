-- Prove2me | solution 1 for TarchaBraids.thm_3_15_adjacent_left_pairwise_separation_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-21T08:57:42.412063+00:00
-- url     : https://prove2.me/submissions/ac6a2941-758e-41ec-be8b-77cff43f7608

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_separation_interfaces_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_left_local_facts_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_outer_outside_facts_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_raw_injective_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_raw_zero_endpoints_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_word_one_endpoints_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_outer_one_endpoint_v1

namespace TarchaBraids

open BraidsLinksMCG

@[simp] lemma braidInterp_re_pairwise_v1 (u : ℝ) (z w : ℂ) :
    (braidInterp u z w).re = (1 - u) * z.re + u * w.re := by
  simp [braidInterp]

@[simp] lemma braidInterp_im_pairwise_v1 (u : ℝ) (z w : ℂ) :
    (braidInterp u z w).im = (1 - u) * z.im + u * w.im := by
  simp [braidInterp]

lemma sin_pi_mul_pos_pairwise_v1 {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 < Real.sin (Real.pi * q) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · nlinarith [Real.pi_pos]

lemma sin_pi_mul_nonneg_pairwise_v1 {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ Real.sin (Real.pi * q) := by
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · positivity
  · nlinarith [Real.pi_pos]

lemma cos_pi_mul_nonneg_first_pairwise_v1 {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    0 ≤ Real.cos (Real.pi * q) := by
  apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

lemma cos_pi_mul_nonpos_final_pairwise_v1 {q : ℝ}
    (hq0 : 3 / 4 < q) (hq1 : q ≤ 1) :
    Real.cos (Real.pi * q) ≤ 0 := by
  apply Real.cos_nonpos_of_pi_div_two_le_of_le
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

lemma adjacent_hi2_pairwise_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) : (i : ℕ) + 2 < n := by
  have hj := j.isLt
  omega

lemma braid_three_distinct_02_pairwise_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) :
    strandIdx i ≠ strandIdxSucc j := by
  intro h
  have hv := congrArg Fin.val h
  simp [strandIdx, strandIdxSucc, hji] at hv
  omega

lemma strandIdx_ne_strandIdxSucc_pairwise_v1 {n : ℕ} (i : Fin (n - 1)) :
    strandIdx i ≠ strandIdxSucc i := by
  intro h
  have hv := congrArg Fin.val h
  simp [strandIdx, strandIdxSucc] at hv

lemma strandIdxSucc_i_ne_strandIdxSucc_j_pairwise_v1 {n : ℕ}
    (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1) :
    strandIdxSucc i ≠ strandIdxSucc j := by
  intro h
  have hv := congrArg Fin.val h
  simp [strandIdxSucc, hji] at hv

lemma leftInterp_first_a_im_neg_pairwise_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) :
    (leftOuterInterpFun n i j u q (strandIdx i)).im < 0 := by
  have hL := thm_3_15_adjacent_left_local_facts_v1 i j hji
  have hO := thm_3_15_adjacent_outer_outside_facts_v1 i j hji
  rw [leftOuterInterpFun, braidInterp_im_pairwise_v1,
    hL.first_a q hq1, hO.outer_a q]
  simp only [twistPoint_im]
  have hsL : 0 ≤ Real.sin (Real.pi * (2 * q)) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hsO : 0 < Real.sin (Real.pi * q) :=
    sin_pi_mul_pos_pairwise_v1 hq0 (by linarith)
  have hnegL : (1 - u) * ((-1) * Real.sin (Real.pi * (2 * q)) / 2) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by nlinarith)
  have hnegO : u * ((-2) * Real.sin (Real.pi * q) / 2) < 0 := by
    exact mul_neg_of_pos_of_neg hu0 (by nlinarith)
  linarith

lemma leftInterp_first_b_im_nonneg_pairwise_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    0 ≤ (leftOuterInterpFun n i j u q (strandIdxSucc i)).im := by
  have hL := thm_3_15_adjacent_left_local_facts_v1 i j hji
  have hO := thm_3_15_adjacent_outer_outside_facts_v1 i j hji
  rw [leftOuterInterpFun, braidInterp_im_pairwise_v1,
    hL.first_b q hq1, hO.outer_b q]
  simp only [twistPoint_im, Complex.ofReal_im]
  have hsL : 0 ≤ Real.sin (Real.pi * (2 * q)) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hnonneg : 0 ≤ (1 - u) * (Real.sin (Real.pi * (2 * q)) / 2) := by
    positivity
  simpa using hnonneg

lemma leftInterp_first_a_re_le_pairwise_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    (leftOuterInterpFun n i j u q (strandIdx i)).re ≤ ((i : ℕ) : ℝ) + 2 := by
  have hL := thm_3_15_adjacent_left_local_facts_v1 i j hji
  have hO := thm_3_15_adjacent_outer_outside_facts_v1 i j hji
  rw [leftOuterInterpFun, braidInterp_re_pairwise_v1,
    hL.first_a q hq1, hO.outer_a q]
  simp only [twistPoint_re]
  have hcL := Real.neg_one_le_cos (Real.pi * (2 * q))
  have hcO := cos_pi_mul_nonneg_first_pairwise_v1 hq0 hq1
  have hz : ((i : ℕ) : ℝ) + 3 / 2 + (-1) * Real.cos (Real.pi * (2 * q)) / 2
      ≤ ((i : ℕ) : ℝ) + 2 := by linarith
  have hw : ((i : ℕ) : ℝ) + 2 + (-2) * Real.cos (Real.pi * q) / 2
      ≤ ((i : ℕ) : ℝ) + 2 := by linarith
  have h1 : 0 ≤ (1 - u) * ((((i : ℕ) : ℝ) + 2) -
      (((i : ℕ) : ℝ) + 3 / 2 + (-1) * Real.cos (Real.pi * (2 * q)) / 2)) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hz)
  have h2 : 0 ≤ u * ((((i : ℕ) : ℝ) + 2) -
      (((i : ℕ) : ℝ) + 2 + (-2) * Real.cos (Real.pi * q) / 2)) :=
    mul_nonneg hu0 (sub_nonneg.mpr hw)
  nlinarith

lemma leftInterp_first_b_re_le_pairwise_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    (leftOuterInterpFun n i j u q (strandIdxSucc i)).re ≤ ((i : ℕ) : ℝ) + 2 := by
  have hL := thm_3_15_adjacent_left_local_facts_v1 i j hji
  have hO := thm_3_15_adjacent_outer_outside_facts_v1 i j hji
  rw [leftOuterInterpFun, braidInterp_re_pairwise_v1,
    hL.first_b q hq1, hO.outer_b q]
  simp only [twistPoint_re, Complex.ofReal_re]
  have hc := Real.cos_le_one (Real.pi * (2 * q))
  have hz : ((i : ℕ) : ℝ) + 3 / 2 + Real.cos (Real.pi * (2 * q)) / 2
      ≤ ((i : ℕ) : ℝ) + 2 := by linarith
  have h1 : 0 ≤ (1 - u) * ((((i : ℕ) : ℝ) + 2) -
      (((i : ℕ) : ℝ) + 3 / 2 + Real.cos (Real.pi * (2 * q)) / 2)) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hz)
  nlinarith

lemma leftInterp_first_c_re_gt_pairwise_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    ((i : ℕ) : ℝ) + 2 <
      (leftOuterInterpFun n i j u q (strandIdxSucc j)).re := by
  have hL := thm_3_15_adjacent_left_local_facts_v1 i j hji
  have hO := thm_3_15_adjacent_outer_outside_facts_v1 i j hji
  rw [leftOuterInterpFun, braidInterp_re_pairwise_v1,
    hL.first_c q hq1, hO.outer_c q]
  simp only [Complex.ofReal_re, twistPoint_re]
  have hc := cos_pi_mul_nonneg_first_pairwise_v1 hq0 hq1
  have hleft : 0 < 1 - u := by linarith
  have hpos : 0 < (1 - u) * 1 := by positivity
  nlinarith

lemma leftInterp_middle_a_im_neg_pairwise_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hq1 : 1 / 2 < q) (hq2 : q ≤ 3 / 4) :
    (leftOuterInterpFun n i j u q (strandIdx i)).im < 0 := by
  have hL := thm_3_15_adjacent_left_local_facts_v1 i j hji
  have hO := thm_3_15_adjacent_outer_outside_facts_v1 i j hji
  have hn1 : ¬ q ≤ 1 / 2 := not_le.mpr hq1
  rw [leftOuterInterpFun, braidInterp_im_pairwise_v1,
    hL.middle_a q hn1 hq2, hO.outer_a q]
  simp only [twistPoint_im]
  have ht0 : 0 ≤ 4 * q - 2 := by linarith
  have ht1 : 4 * q - 2 ≤ 1 := by linarith
  have hsL := sin_pi_mul_nonneg_pairwise_v1 ht0 ht1
  have hsO := sin_pi_mul_pos_pairwise_v1 (q := q) (by linarith) (by linarith)
  have hnegL : (1 - u) * ((-1) * Real.sin (Real.pi * (4 * q - 2)) / 2) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by nlinarith)
  have hnegO : u * ((-2) * Real.sin (Real.pi * q) / 2) < 0 := by
    exact mul_neg_of_pos_of_neg hu0 (by nlinarith)
  linarith

lemma leftInterp_middle_b_im_zero_pairwise_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hq1 : 1 / 2 < q) (hq2 : q ≤ 3 / 4) :
    (leftOuterInterpFun n i j u q (strandIdxSucc i)).im = 0 := by
  have hL := thm_3_15_adjacent_left_local_facts_v1 i j hji
  have hO := thm_3_15_adjacent_outer_outside_facts_v1 i j hji
  have hn1 : ¬ q ≤ 1 / 2 := not_le.mpr hq1
  rw [leftOuterInterpFun, braidInterp_im_pairwise_v1,
    hL.middle_b q hn1 hq2, hO.outer_b q]
  simp

lemma leftInterp_middle_c_im_pos_pairwise_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hq1 : 1 / 2 < q) (hq2 : q ≤ 3 / 4) :
    0 < (leftOuterInterpFun n i j u q (strandIdxSucc j)).im := by
  have hL := thm_3_15_adjacent_left_local_facts_v1 i j hji
  have hO := thm_3_15_adjacent_outer_outside_facts_v1 i j hji
  have hn1 : ¬ q ≤ 1 / 2 := not_le.mpr hq1
  rw [leftOuterInterpFun, braidInterp_im_pairwise_v1,
    hL.middle_c q hn1 hq2, hO.outer_c q]
  simp only [twistPoint_im]
  have ht0 : 0 ≤ 4 * q - 2 := by linarith
  have ht1 : 4 * q - 2 ≤ 1 := by linarith
  have hsL := sin_pi_mul_nonneg_pairwise_v1 ht0 ht1
  have hsO := sin_pi_mul_pos_pairwise_v1 (q := q) (by linarith) (by linarith)
  have hposL : 0 ≤ (1 - u) * (Real.sin (Real.pi * (4 * q - 2)) / 2) := by positivity
  have hposO : 0 < u * (2 * Real.sin (Real.pi * q) / 2) := by positivity
  linarith

lemma leftInterp_final_a_re_gt_pairwise_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hq0 : 3 / 4 < q) (hq1 : q ≤ 1) :
    ((i : ℕ) : ℝ) + 2 <
      (leftOuterInterpFun n i j u q (strandIdx i)).re := by
  have hL := thm_3_15_adjacent_left_local_facts_v1 i j hji
  have hO := thm_3_15_adjacent_outer_outside_facts_v1 i j hji
  have hn1 : ¬ q ≤ 1 / 2 := by linarith
  have hn2 : ¬ q ≤ 3 / 4 := not_le.mpr hq0
  rw [leftOuterInterpFun, braidInterp_re_pairwise_v1,
    hL.final_a q hn1 hn2, hO.outer_a q]
  simp only [Complex.ofReal_re, twistPoint_re]
  have hc := cos_pi_mul_nonpos_final_pairwise_v1 hq0 hq1
  have hleft : 0 < 1 - u := by linarith
  have hpos : 0 < (1 - u) * 1 := by positivity
  nlinarith

lemma leftInterp_final_b_re_le_pairwise_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hq0 : 3 / 4 < q) (hq1 : q ≤ 1) :
    (leftOuterInterpFun n i j u q (strandIdxSucc i)).re ≤ ((i : ℕ) : ℝ) + 2 := by
  have hL := thm_3_15_adjacent_left_local_facts_v1 i j hji
  have hO := thm_3_15_adjacent_outer_outside_facts_v1 i j hji
  have hn1 : ¬ q ≤ 1 / 2 := by linarith
  have hn2 : ¬ q ≤ 3 / 4 := not_le.mpr hq0
  rw [leftOuterInterpFun, braidInterp_re_pairwise_v1,
    hL.final_b q hn1 hn2, hO.outer_b q]
  simp only [twistPoint_re, Complex.ofReal_re]
  have hc := Real.neg_one_le_cos (Real.pi * (4 * q - 3))
  have hz : ((i : ℕ) : ℝ) + 3 / 2 + (-1) * Real.cos (Real.pi * (4 * q - 3)) / 2
      ≤ ((i : ℕ) : ℝ) + 2 := by linarith
  have hprod : 0 ≤ (1 - u) * ((((i : ℕ) : ℝ) + 2) -
      (((i : ℕ) : ℝ) + 3 / 2 + (-1) * Real.cos (Real.pi * (4 * q - 3)) / 2)) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hz)
  nlinarith

lemma leftInterp_final_c_re_le_pairwise_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hq0 : 3 / 4 < q) (hq1 : q ≤ 1) :
    (leftOuterInterpFun n i j u q (strandIdxSucc j)).re ≤ ((i : ℕ) : ℝ) + 2 := by
  have hL := thm_3_15_adjacent_left_local_facts_v1 i j hji
  have hO := thm_3_15_adjacent_outer_outside_facts_v1 i j hji
  have hn1 : ¬ q ≤ 1 / 2 := by linarith
  have hn2 : ¬ q ≤ 3 / 4 := not_le.mpr hq0
  rw [leftOuterInterpFun, braidInterp_re_pairwise_v1,
    hL.final_c q hn1 hn2, hO.outer_c q]
  simp only [twistPoint_re]
  have hcL := Real.cos_le_one (Real.pi * (4 * q - 3))
  have hcO := cos_pi_mul_nonpos_final_pairwise_v1 hq0 hq1
  have hz : ((i : ℕ) : ℝ) + 3 / 2 + Real.cos (Real.pi * (4 * q - 3)) / 2
      ≤ ((i : ℕ) : ℝ) + 2 := by linarith
  have hw : ((i : ℕ) : ℝ) + 2 + 2 * Real.cos (Real.pi * q) / 2
      ≤ ((i : ℕ) : ℝ) + 2 := by linarith
  have h1 : 0 ≤ (1 - u) * ((((i : ℕ) : ℝ) + 2) -
      (((i : ℕ) : ℝ) + 3 / 2 + Real.cos (Real.pi * (4 * q - 3)) / 2)) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hz)
  have h2 : 0 ≤ u * ((((i : ℕ) : ℝ) + 2) -
      (((i : ℕ) : ℝ) + 2 + 2 * Real.cos (Real.pi * q) / 2)) :=
    mul_nonneg hu0 (sub_nonneg.mpr hw)
  nlinarith

lemma leftInterp_final_b_im_neg_pairwise_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hq0 : 3 / 4 < q) (hq1 : q < 1) :
    (leftOuterInterpFun n i j u q (strandIdxSucc i)).im < 0 := by
  have hL := thm_3_15_adjacent_left_local_facts_v1 i j hji
  have hO := thm_3_15_adjacent_outer_outside_facts_v1 i j hji
  have hn1 : ¬ q ≤ 1 / 2 := by linarith
  have hn2 : ¬ q ≤ 3 / 4 := not_le.mpr hq0
  rw [leftOuterInterpFun, braidInterp_im_pairwise_v1,
    hL.final_b q hn1 hn2, hO.outer_b q]
  simp only [twistPoint_im, Complex.ofReal_im]
  have ht0 : 0 < 4 * q - 3 := by linarith
  have ht1 : 4 * q - 3 < 1 := by linarith
  have hs := sin_pi_mul_pos_pairwise_v1 ht0 ht1
  have hcoef : 0 < 1 - u := by linarith
  have hneg : (1 - u) * ((-1) * Real.sin (Real.pi * (4 * q - 3)) / 2) < 0 := by
    exact mul_neg_of_pos_of_neg hcoef (by nlinarith)
  simpa using hneg

lemma leftInterp_final_c_im_nonneg_pairwise_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hq0 : 3 / 4 < q) (hq1 : q ≤ 1) :
    0 ≤ (leftOuterInterpFun n i j u q (strandIdxSucc j)).im := by
  have hL := thm_3_15_adjacent_left_local_facts_v1 i j hji
  have hO := thm_3_15_adjacent_outer_outside_facts_v1 i j hji
  have hn1 : ¬ q ≤ 1 / 2 := by linarith
  have hn2 : ¬ q ≤ 3 / 4 := not_le.mpr hq0
  rw [leftOuterInterpFun, braidInterp_im_pairwise_v1,
    hL.final_c q hn1 hn2, hO.outer_c q]
  simp only [twistPoint_im]
  have ht0 : 0 ≤ 4 * q - 3 := by linarith
  have ht1 : 4 * q - 3 ≤ 1 := by linarith
  have hsL := sin_pi_mul_nonneg_pairwise_v1 ht0 ht1
  have hsO := sin_pi_mul_nonneg_pairwise_v1 (by linarith : 0 ≤ q) hq1
  have hL' : 0 ≤ (1 - u) * (Real.sin (Real.pi * (4 * q - 3)) / 2) := by positivity
  have hO' : 0 ≤ u * (2 * Real.sin (Real.pi * q) / 2) := by positivity
  linarith

lemma leftInterp_local01_ne_pairwise_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    leftOuterInterpFun n i j u q (strandIdx i) ≠
      leftOuterInterpFun n i j u q (strandIdxSucc i) := by
  by_cases huZ : u = 0
  · subst u
    intro h
    have heq := thm_3_15_adjacent_raw_injective_v1.1 i j q (by
      simpa [leftOuterInterpFun, braidInterp] using h)
    exact strandIdx_ne_strandIdxSucc_pairwise_v1 i heq
  by_cases huO : u = 1
  · subst u
    intro h
    have hi2 := adjacent_hi2_pairwise_v1 i j hji
    have heq := thm_3_15_adjacent_raw_injective_v1.2.2 i q hi2 (by
      simpa [leftOuterInterpFun, braidInterp] using h)
    exact strandIdx_ne_strandIdxSucc_pairwise_v1 i heq
  have huP : 0 < u := lt_of_le_of_ne hu0 (Ne.symm huZ)
  have huL : u < 1 := lt_of_le_of_ne hu1 huO
  by_cases hfirst : q ≤ 1 / 2
  · by_cases hqZ : q = 0
    · subst q
      have hL0 := thm_3_15_adjacent_raw_zero_endpoints_v1.1 n i j
      have hO0 := thm_3_15_adjacent_raw_zero_endpoints_v1.2.2 n i
      have hinterp0 :
          leftOuterInterpFun n i j u 0 = (baseOrdered n).1 := by
        funext k
        rw [leftOuterInterpFun, congrFun hL0 k, congrFun hO0 k]
        unfold braidInterp
        module
      intro h
      rw [congrFun hinterp0 (strandIdx i),
        congrFun hinterp0 (strandIdxSucc i)] at h
      have heq := (baseOrdered n).2 h
      exact strandIdx_ne_strandIdxSucc_pairwise_v1 i heq
    · have hqP : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqZ)
      intro h
      have him := congrArg Complex.im h
      have ha := leftInterp_first_a_im_neg_pairwise_v1 i j hji u q huP huL hqP hfirst
      have hb := leftInterp_first_b_im_nonneg_pairwise_v1 i j hji u q hu0 hu1 hq0 hfirst
      linarith
  · have hqP : 1 / 2 < q := lt_of_not_ge hfirst
    by_cases hmiddle : q ≤ 3 / 4
    · intro h
      have him := congrArg Complex.im h
      have ha := leftInterp_middle_a_im_neg_pairwise_v1 i j hji u q huP huL hqP hmiddle
      have hb := leftInterp_middle_b_im_zero_pairwise_v1 i j hji u q hqP hmiddle
      linarith
    · have hqF : 3 / 4 < q := lt_of_not_ge hmiddle
      intro h
      have hre := congrArg Complex.re h
      have ha := leftInterp_final_a_re_gt_pairwise_v1 i j hji u q hu0 huL hqF hq1
      have hb := leftInterp_final_b_re_le_pairwise_v1 i j hji u q hu0 hu1 hqF hq1
      linarith

lemma leftInterp_local02_ne_pairwise_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    leftOuterInterpFun n i j u q (strandIdx i) ≠
      leftOuterInterpFun n i j u q (strandIdxSucc j) := by
  by_cases huZ : u = 0
  · subst u
    intro h
    have heq := thm_3_15_adjacent_raw_injective_v1.1 i j q (by
      simpa [leftOuterInterpFun, braidInterp] using h)
    exact braid_three_distinct_02_pairwise_v1 i j hji heq
  by_cases huO : u = 1
  · subst u
    intro h
    have hi2 := adjacent_hi2_pairwise_v1 i j hji
    have heq := thm_3_15_adjacent_raw_injective_v1.2.2 i q hi2 (by
      simpa [leftOuterInterpFun, braidInterp] using h)
    exact braid_three_distinct_02_pairwise_v1 i j hji heq
  have huP : 0 < u := lt_of_le_of_ne hu0 (Ne.symm huZ)
  have huL : u < 1 := lt_of_le_of_ne hu1 huO
  by_cases hfirst : q ≤ 1 / 2
  · intro h
    have hre := congrArg Complex.re h
    have ha := leftInterp_first_a_re_le_pairwise_v1 i j hji u q hu0 hu1 hq0 hfirst
    have hc := leftInterp_first_c_re_gt_pairwise_v1 i j hji u q hu0 huL hq0 hfirst
    linarith
  · have hqP : 1 / 2 < q := lt_of_not_ge hfirst
    by_cases hmiddle : q ≤ 3 / 4
    · intro h
      have him := congrArg Complex.im h
      have ha := leftInterp_middle_a_im_neg_pairwise_v1 i j hji u q huP huL hqP hmiddle
      have hc := leftInterp_middle_c_im_pos_pairwise_v1 i j hji u q huP huL hqP hmiddle
      linarith
    · have hqF : 3 / 4 < q := lt_of_not_ge hmiddle
      intro h
      have hre := congrArg Complex.re h
      have ha := leftInterp_final_a_re_gt_pairwise_v1 i j hji u q hu0 huL hqF hq1
      have hc := leftInterp_final_c_re_le_pairwise_v1 i j hji u q hu0 hu1 hqF hq1
      linarith

lemma leftInterp_local12_ne_pairwise_v1 {n : ℕ} (i j : Fin (n - 1))
    (hji : (j : ℕ) = (i : ℕ) + 1) (u q : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    leftOuterInterpFun n i j u q (strandIdxSucc i) ≠
      leftOuterInterpFun n i j u q (strandIdxSucc j) := by
  by_cases huZ : u = 0
  · subst u
    intro h
    have heq := thm_3_15_adjacent_raw_injective_v1.1 i j q (by
      simpa [leftOuterInterpFun, braidInterp] using h)
    exact strandIdxSucc_i_ne_strandIdxSucc_j_pairwise_v1 i j hji heq
  by_cases huO : u = 1
  · subst u
    intro h
    have hi2 := adjacent_hi2_pairwise_v1 i j hji
    have heq := thm_3_15_adjacent_raw_injective_v1.2.2 i q hi2 (by
      simpa [leftOuterInterpFun, braidInterp] using h)
    exact strandIdxSucc_i_ne_strandIdxSucc_j_pairwise_v1 i j hji heq
  have huP : 0 < u := lt_of_le_of_ne hu0 (Ne.symm huZ)
  have huL : u < 1 := lt_of_le_of_ne hu1 huO
  by_cases hfirst : q ≤ 1 / 2
  · intro h
    have hre := congrArg Complex.re h
    have hb := leftInterp_first_b_re_le_pairwise_v1 i j hji u q hu0 hu1 hq0 hfirst
    have hc := leftInterp_first_c_re_gt_pairwise_v1 i j hji u q hu0 huL hq0 hfirst
    linarith
  · have hqP : 1 / 2 < q := lt_of_not_ge hfirst
    by_cases hmiddle : q ≤ 3 / 4
    · intro h
      have him := congrArg Complex.im h
      have hb := leftInterp_middle_b_im_zero_pairwise_v1 i j hji u q hqP hmiddle
      have hc := leftInterp_middle_c_im_pos_pairwise_v1 i j hji u q huP huL hqP hmiddle
      linarith
    · have hqF : 3 / 4 < q := lt_of_not_ge hmiddle
      by_cases hqO : q = 1
      · subst q
        have hi2 := adjacent_hi2_pairwise_v1 i j hji
        have hword := (thm_3_15_adjacent_word_one_endpoints_v1 i j hji).1
        have houter := thm_3_15_adjacent_outer_one_endpoint_v1 i j hji hi2
        have hinterp :
            leftOuterInterpFun n i j u 1 = leftBraidFun n i j 1 := by
          funext k
          rw [leftOuterInterpFun]
          have hk : outerRotateFun n i 1 k = leftBraidFun n i j 1 k := by
            rw [congrFun houter k, congrFun hword k]
          rw [hk]
          unfold braidInterp
          module
        intro h
        rw [congrFun hinterp (strandIdxSucc i),
          congrFun hinterp (strandIdxSucc j)] at h
        have heq := thm_3_15_adjacent_raw_injective_v1.1 i j 1 h
        exact strandIdxSucc_i_ne_strandIdxSucc_j_pairwise_v1 i j hji heq
      · have hqLt : q < 1 := lt_of_le_of_ne hq1 hqO
        intro h
        have him := congrArg Complex.im h
        have hb := leftInterp_final_b_im_neg_pairwise_v1 i j hji u q hu0 huL hqF hqLt
        have hc := leftInterp_final_c_im_nonneg_pairwise_v1 i j hji u q hu0 hu1 hqF hq1
        linarith

end TarchaBraids

open BraidsLinksMCG TarchaBraids

theorem solution :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      AdjacentLeftPairwiseSeparationFacts i j hji := by
  intro n i j hji
  exact {
    local01_ne := fun u q hu0 hu1 hq0 hq1 =>
      leftInterp_local01_ne_pairwise_v1 i j hji u q hu0 hu1 hq0 hq1
    local02_ne := fun u q hu0 hu1 hq0 hq1 =>
      leftInterp_local02_ne_pairwise_v1 i j hji u q hu0 hu1 hq0 hq1
    local12_ne := fun u q hu0 hu1 hq0 hq1 =>
      leftInterp_local12_ne_pairwise_v1 i j hji u q hu0 hu1 hq0 hq1
  }
