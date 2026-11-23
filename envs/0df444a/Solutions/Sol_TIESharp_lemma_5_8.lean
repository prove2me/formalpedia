-- Prove2me | solution 1 for TIESharp.lemma_5_8
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:58:30.763796+00:00
-- url     : https://prove2.me/submissions/1837fce1-d1d3-4e25-9805-00cb1ce8c34b

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000

theorem solution (θ : Fin 7 → ℝ) (hθnn : ∀ l, 0 ≤ θ l) (hθsum : ∑ l, θ l = 1)
    (hθ₁ : 3 / 4 ≤ Real.sqrt (∑ l, θ l ^ 2)) (hθ₂ : Real.sqrt (∑ l, θ l ^ 2) ≤ 1)
    (i : Fin 7) (hi : ∀ l, θ l ≤ θ i) (d : ℝ) (hd₁ : 1 ≤ d) (hd₂ : d ≤ 2) :
    (2 - d) * θ i * (1 - θ i)
      + (max ((d + 1) * θ i - Real.sqrt (∑ l, θ l ^ 2) - 1) 0) ^ 2
        / (4 * ((d ^ 2 + 1) * Real.sqrt (∑ l, θ l ^ 2) + 1 - (d + 1) * θ i))
      ≥ 2 * (1 - Real.sqrt (∑ l, θ l ^ 2)) * (Real.sqrt (∑ l, θ l ^ 2) - 3 / 4) := by
  let S : ℝ := ∑ l, θ l ^ 2
  let r : ℝ := Real.sqrt S
  let x : ℝ := θ i
  change (2 - d) * x * (1 - x) + (max ((d + 1) * x - r - 1) 0) ^ 2
      / (4 * ((d ^ 2 + 1) * r + 1 - (d + 1) * x))
    ≥ 2 * (1 - r) * (r - 3 / 4)
  have hS0 : 0 ≤ S := by
    dsimp [S]
    positivity
  have hr0 : 0 ≤ r := Real.sqrt_nonneg S
  have hr2 : r ^ 2 = S := Real.sq_sqrt hS0
  have hr34 : 3 / 4 ≤ r := hθ₁
  have hr1 : r ≤ 1 := hθ₂
  have hx0 : 0 ≤ x := hθnn i
  have hxr2 : x ^ 2 ≤ r ^ 2 := by
    rw [hr2]
    dsimp [S, x]
    exact Finset.single_le_sum (fun l _ => sq_nonneg (θ l)) (Finset.mem_univ i)
  have hxr : x ≤ r := (sq_le_sq₀ hx0 hr0).mp hxr2
  have hr2x : r ^ 2 ≤ x := by
    rw [hr2]
    calc
      S = ∑ l, θ l * θ l := by
        dsimp [S]
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ ≤ ∑ l, x * θ l := by
        apply Finset.sum_le_sum
        intro l _
        exact mul_le_mul_of_nonneg_right (hi l) (hθnn l)
      _ = x * ∑ l, θ l := by rw [Finset.mul_sum]
      _ = x := by rw [hθsum, mul_one]
  have hx1 : x ≤ 1 := hxr.trans hr1
  have hx12 : 1 / 2 ≤ x := by nlinarith only [hr2x, hr34]
  have hsum_erase : ∑ l ∈ Finset.univ.erase i, θ l = 1 - x := by
    have h := Finset.sum_erase_add Finset.univ θ (Finset.mem_univ i)
    rw [hθsum] at h
    dsimp [x]
    linarith only [h]
  have hS_eq : S = x ^ 2 + ∑ l ∈ Finset.univ.erase i, θ l ^ 2 := by
    have h := Finset.sum_erase_add Finset.univ (fun l => θ l ^ 2) (Finset.mem_univ i)
    dsimp [S, x]
    linarith only [h]
  have hother : (∑ l ∈ Finset.univ.erase i, θ l ^ 2) ≤ (1 - x) ^ 2 := by
    calc
      (∑ l ∈ Finset.univ.erase i, θ l ^ 2) ≤ (∑ l ∈ Finset.univ.erase i, θ l) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg (fun l _ => hθnn l)
      _ = (1 - x) ^ 2 := by rw [hsum_erase]
  have hquad : r ^ 2 ≤ 2 * x ^ 2 - 2 * x + 1 := by
    nlinarith only [hr2, hS_eq, hother]

  let D : ℝ := (d ^ 2 + 1) * r + 1 - (d + 1) * x
  let B : ℝ := 5 * r + 1 - 3 * x
  have hDpos : 0 < D := by
    have hfac : 0 ≤ (d - 1) * ((d + 1) * r - x) := by
      apply mul_nonneg (sub_nonneg.mpr hd₁)
      nlinarith only [hd₁, hr0, hxr]
    dsimp [D]
    nlinarith only [hfac, hxr]
  have hDB : D ≤ B := by
    have hfac : 0 ≤ (2 - d) * ((2 + d) * r - x) := by
      apply mul_nonneg (sub_nonneg.mpr hd₂)
      nlinarith only [hd₁, hr0, hxr]
    dsimp [D, B]
    nlinarith only [hfac]
  have hBpos : 0 < B := lt_of_lt_of_le hDpos hDB

  have hmaster (α : ℝ) (hα0 : 0 ≤ α) (hαx : α ≤ 1 - x) :
      α * (3 * x - r - 1) - α ^ 2 * B ≤
        (2 - d) * x * (1 - x) + (max ((d + 1) * x - r - 1) 0) ^ 2 / (4 * D) := by
    let z : ℝ := (d + 1) * x - r - 1
    have hfrac : α * z - B * α ^ 2 ≤ (max z 0) ^ 2 / (4 * B) := by
      rcases le_total 0 z with hz | hz
      · rw [max_eq_left hz]
        rw [le_div_iff₀ (by positivity : 0 < 4 * B)]
        nlinarith only [sq_nonneg (z - 2 * α * B)]
      · rw [max_eq_right hz]
        norm_num
        nlinarith only [mul_nonneg hα0 (neg_nonneg.mpr hz), mul_nonneg hBpos.le (sq_nonneg α)]
    have h4Dpos : 0 < 4 * D := mul_pos (by norm_num) hDpos
    have h4DB : 4 * D ≤ 4 * B := by linarith only [hDB]
    have hfrac' : (max z 0) ^ 2 / (4 * D) ≥ α * z - B * α ^ 2 := by
      calc
        α * z - B * α ^ 2 ≤ (max z 0) ^ 2 / (4 * B) := hfrac
        _ ≤ (max z 0) ^ 2 / (4 * D) := by
          exact div_le_div_of_nonneg_left (sq_nonneg _) h4Dpos h4DB
    have hnonneg : 0 ≤ (2 - d) * x * (1 - x - α) := by
      exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hd₂) hx0) (sub_nonneg.mpr hαx)
    dsimp [z] at hfrac'
    calc
      α * (3 * x - r - 1) - α ^ 2 * B =
          (2 - d) * x * (1 - x) + (α * ((d + 1) * x - r - 1) - B * α ^ 2)
            - (2 - d) * x * (1 - x - α) := by ring
      _ ≤ (2 - d) * x * (1 - x) + (α * ((d + 1) * x - r - 1) - B * α ^ 2) := by
        linarith only [hnonneg]
      _ ≤ (2 - d) * x * (1 - x) + (max ((d + 1) * x - r - 1) 0) ^ 2 / (4 * D) :=
        add_le_add_right hfrac' _

  change (2 - d) * x * (1 - x) + (max ((d + 1) * x - r - 1) 0) ^ 2 / (4 * D)
    ≥ 2 * (1 - r) * (r - 3 / 4)
  by_cases hr : r ≤ 9 / 10
  · let s : ℝ := Real.sqrt (2 * r ^ 2 - 1)
    have hsq : s ^ 2 = 2 * r ^ 2 - 1 := Real.sq_sqrt (by nlinarith only [hr34])
    have h21x : 0 ≤ 2 * x - 1 := by linarith only [hx12]
    have hsx : s ≤ 2 * x - 1 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · exact h21x
      · nlinarith only [hquad, hsq]
    have hxlow : (1 + s) / 2 ≤ x := by linarith only [hsx]
    have hscalar : 200 * (1 - r) * (r - 3 / 4) ≤ 33 * x - 15 * r - 11 := by
      by_cases hr8 : r ≤ 4 / 5
      · have hprod : 0 ≤ (r - 3 / 4) * (4 / 5 - r) :=
          mul_nonneg (sub_nonneg.mpr hr34) (sub_nonneg.mpr hr8)
        have hline0 : 0 ≤ (351 / 100 : ℝ) * r - 57 / 25 := by linarith only [hr34]
        have hline : (351 / 100 : ℝ) * r - 57 / 25 ≤ s := by
          change (351 / 100 : ℝ) * r - 57 / 25 ≤ Real.sqrt (2 * r ^ 2 - 1)
          apply (Real.le_sqrt hline0 (by nlinarith only [hr34])).mpr
          nlinarith only [hprod]
        nlinarith only [hxlow, hline, sq_nonneg (r - 61417 / 80000)]
      · have hr8' : 4 / 5 ≤ r := le_of_lt (lt_of_not_ge hr8)
        have hprod : 0 ≤ (r - 4 / 5) * (9 / 10 - r) :=
          mul_nonneg (sub_nonneg.mpr hr8') (sub_nonneg.mpr hr)
        have hline0 : 0 ≤ (129 / 50 : ℝ) * r - 1537 / 1000 := by linarith only [hr8']
        have hline : (129 / 50 : ℝ) * r - 1537 / 1000 ≤ s := by
          change (129 / 50 : ℝ) * r - 1537 / 1000 ≤ Real.sqrt (2 * r ^ 2 - 1)
          apply (Real.le_sqrt hline0 (by nlinarith only [hr8'])).mpr
          nlinarith only [hprod]
        nlinarith only [hxlow, hline, sq_nonneg (r - 806075 / 1000000)]
    have hm := hmaster (1 / 10) (by norm_num) (by linarith only [hxr, hr])
    dsimp [B] at hm
    nlinarith only [hm, hscalar]
  · have hr9 : 9 / 10 ≤ r := le_of_lt (lt_of_not_ge hr)
    have hx81 : 81 / 100 ≤ x := by nlinarith only [hr2x, hr9]
    have hxsecond : (5 * r - 1) / 4 ≤ x := by
      have hp : 0 ≤ (x - 4 / 5) * (1 - x) :=
        mul_nonneg (by linarith only [hx81]) (sub_nonneg.mpr hx1)
      nlinarith only [hquad, hp, sq_nonneg (1 - r)]
    have hcoef : 0 ≤ 3 * (2 - r) := by linarith only [hr1]
    have hp := mul_le_mul_of_nonneg_left hxsecond hcoef
    have hq : 0 ≤ (r - 9 / 10) * (5 * r + 19 / 2) :=
      mul_nonneg (sub_nonneg.mpr hr9) (by linarith only [hr9])
    have hbracket : 0 ≤ 3 * (2 - r) * x + 5 * r ^ 2 - 7 * r - 1 / 2 := by
      nlinarith only [hp, hq]
    have hm := hmaster (1 - r) (sub_nonneg.mpr hr1) (by linarith only [hxr])
    dsimp [B] at hm
    calc
      2 * (1 - r) * (r - 3 / 4)
          ≤ (1 - r) * (3 * x - r - 1) - (1 - r) ^ 2 * (5 * r + 1 - 3 * x) := by
            have hspare : 0 ≤ (1 - r) *
                (3 * (2 - r) * x + 5 * r ^ 2 - 7 * r - 1 / 2) :=
              mul_nonneg (sub_nonneg.mpr hr1) hbracket
            nlinarith only [hspare]
      _ ≤ (2 - d) * x * (1 - x) + (max ((d + 1) * x - r - 1) 0) ^ 2 / (4 * D) := hm
