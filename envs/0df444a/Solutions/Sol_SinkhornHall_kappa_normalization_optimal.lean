-- Prove2me | solution 1 for SinkhornHall.kappa_normalization_optimal
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T23:58:04.429455+00:00
-- url     : https://prove2.me/submissions/1ba2635f-d459-4622-9d56-30f1f65cf15c

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis

open Finset SinkhornHall

private lemma log_le_sub_one_sh {x : ℝ} (hx : 0 < x) : Real.log x ≤ x - 1 := by
  have h := Real.log_le_log hx (by linarith [Real.add_one_le_exp (x - 1)] : x ≤ Real.exp (x - 1))
  rwa [Real.log_exp] at h

private lemma weighted_am_gm {α : Type*} [Fintype α] [Nonempty α]
    (w u : α → ℝ) (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (hu : ∀ i, 0 < u i) :
    ∏ i, u i ^ w i ≤ ∑ i, w i * u i := by
  let S : ℝ := ∑ i, w i * u i
  have hS_pos : 0 < S :=
    Finset.sum_pos (fun i _ => mul_pos (hw i) (hu i)) Finset.univ_nonempty
  have hprod_pos : 0 < ∏ i, u i ^ w i :=
    Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hu i) (w i)
  have hlog_prod : Real.log (∏ i, u i ^ w i) = ∑ i, w i * Real.log (u i) := by
    rw [Real.log_prod fun i _ => (Real.rpow_pos_of_pos (hu i) (w i)).ne']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.log_rpow (hu i), mul_comm]
  have hdiff : Real.log (∏ i, u i ^ w i) - Real.log S ≤ 0 := by
    have h1 : Real.log (∏ i, u i ^ w i) - Real.log S =
        ∑ i, w i * Real.log (u i / S) := by
      rw [hlog_prod, ← one_mul (Real.log S), ← hw1, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.log_div (hu i).ne' hS_pos.ne', mul_sub]
    rw [h1]
    have h2 : ∑ i, w i * Real.log (u i / S) ≤ ∑ i, w i * (u i / S - 1) :=
      Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (log_le_sub_one_sh (div_pos (hu i) hS_pos)) (hw i).le
    have h3 : ∑ i, w i * (u i / S - 1) = 0 := by
      have : ∑ i, w i * (u i / S - 1) = (∑ i, w i * u i) / S - ∑ i, w i := by
        simp only [mul_sub, mul_one, Finset.sum_sub_distrib, Finset.sum_div]
        congr 1
        refine Finset.sum_congr rfl fun i _ => (mul_div_assoc (w i) (u i) S).symm
      rw [this, hw1]
      dsimp [S]
      rw [div_self hS_pos.ne', sub_self]
    linarith
  exact (Real.log_le_log_iff hprod_pos hS_pos).mp (by linarith)

theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]
    (A : Matrix ι κ ℝ) (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∃ j, 0 < A i j)
    (hcol : ∀ j, ∃ i, 0 < A i j)
    (r : ι → ℝ) (c : κ → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hRC : ∑ i, r i = ∑ j, c j) (x : ι → ℝ) (y : κ → ℝ) (hx : ∀ i, 0 < x i)
    (hy : ∀ j, 0 < y j) :
    kappa A r c (rowNorm A r y) y ≤ kappa A r c x y ∧
      kappa A r c x (colNorm A c x) ≤ kappa A r c x y := by
  let _ := hRC
  have hne_κ : Nonempty κ := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    obtain ⟨j₀, _⟩ := hrow i₀
    exact ⟨j₀⟩
  let R : ℝ := ∑ i, r i
  let C : ℝ := ∑ j, c j
  have hR_pos : 0 < R := Finset.sum_pos (fun i _ => hr i) Finset.univ_nonempty
  have hC_pos : 0 < C := Finset.sum_pos (fun j _ => hc j) Finset.univ_nonempty
  let s : ι → ℝ := fun i => ∑ j, A i j * y j
  have hs_pos : ∀ i, 0 < s i := by
    intro i
    obtain ⟨j₀, hj₀⟩ := hrow i
    exact (mul_pos hj₀ (hy j₀)).trans_le
      (Finset.single_le_sum (f := fun j => A i j * y j)
        (fun j _ => mul_nonneg (hA i j) (hy j).le) (Finset.mem_univ j₀))
  let t : κ → ℝ := fun j => ∑ i, A i j * x i
  have ht_pos : ∀ j, 0 < t j := by
    intro j
    obtain ⟨i₀, hi₀⟩ := hcol j
    exact (mul_pos hi₀ (hx i₀)).trans_le
      (Finset.single_le_sum (f := fun i => A i j * x i)
        (fun i _ => mul_nonneg (hA i j) (hx i).le) (Finset.mem_univ i₀))
  have hpy_pos : 0 < ∏ j, y j ^ (c j / C) :=
    Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hy j) _
  have hpx_pos : 0 < ∏ i, x i ^ (r i / R) :=
    Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx i) _
  refine ⟨?_, ?_⟩
  · have hpr_pos : 0 < ∏ i, (rowNorm A r y i) ^ (r i / R) :=
      Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (div_pos (hr i) (hs_pos i)) _
    have hnum_row : ∑ i, ∑ j, A i j * rowNorm A r y i * y j = R := by
      have h1 : ∀ i, ∑ j, A i j * rowNorm A r y i * y j = rowNorm A r y i * s i := by
        intro i
        dsimp [s]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      simp_rw [h1]
      dsimp [R, rowNorm]
      refine Finset.sum_congr rfl fun i _ => div_mul_cancel₀ (r i) (hs_pos i).ne'
    have hnum_xy : ∑ i, ∑ j, A i j * x i * y j = ∑ i, x i * s i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp [s]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    let w : ι → ℝ := fun i => r i / R
    let u : ι → ℝ := fun i => x i * s i / r i
    have hw_pos : ∀ i, 0 < w i := fun i => div_pos (hr i) hR_pos
    have hw_sum : ∑ i, w i = 1 := by
      dsimp [w]
      rw [← Finset.sum_div]
      exact div_self hR_pos.ne'
    have hu_pos : ∀ i, 0 < u i := fun i => div_pos (mul_pos (hx i) (hs_pos i)) (hr i)
    have hamgm := weighted_am_gm w u hw_pos hw_sum hu_pos
    have hwu_sum : ∑ i, w i * u i = (∑ i, x i * s i) / R := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp [w, u]
      have hri : r i ≠ 0 := (hr i).ne'
      field_simp [hri]
    have hwu_prod : ∏ i, u i ^ w i =
        (∏ i, x i ^ (r i / R)) / (∏ i, (rowNorm A r y i) ^ (r i / R)) := by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      dsimp [u, w, rowNorm]
      have hx_div : x i * s i / r i = x i / (r i / s i) := by
        have hri : r i ≠ 0 := (hr i).ne'
        have hsi : s i ≠ 0 := (hs_pos i).ne'
        field_simp [hri, hsi]
      rw [hx_div, Real.div_rpow (hx i).le (div_pos (hr i) (hs_pos i)).le]
    rw [hwu_sum, hwu_prod] at hamgm
    unfold kappa
    change (∑ i, ∑ j, A i j * rowNorm A r y i * y j) /
        ((∏ i, rowNorm A r y i ^ (r i / R)) * ∏ j, y j ^ (c j / C)) ≤
      (∑ i, ∑ j, A i j * x i * y j) /
        ((∏ i, x i ^ (r i / R)) * ∏ j, y j ^ (c j / C))
    rw [hnum_row, hnum_xy]
    rw [div_le_div_iff₀ (mul_pos hpr_pos hpy_pos) (mul_pos hpx_pos hpy_pos)]
    rw [div_le_div_iff₀ hpr_pos hR_pos] at hamgm
    nlinarith [hpy_pos]
  · have hpc_pos : 0 < ∏ j, (colNorm A c x j) ^ (c j / C) :=
      Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (div_pos (hc j) (ht_pos j)) _
    have hnum_col : ∑ i, ∑ j, A i j * x i * colNorm A c x j = C := by
      rw [Finset.sum_comm]
      have h1 : ∀ j, ∑ i, A i j * x i * colNorm A c x j = colNorm A c x j * t j := by
        intro j
        dsimp [t]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
      simp_rw [h1]
      dsimp [C, colNorm]
      refine Finset.sum_congr rfl fun j _ => div_mul_cancel₀ (c j) (ht_pos j).ne'
    have hnum_xy : ∑ i, ∑ j, A i j * x i * y j = ∑ j, y j * t j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp [t]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    let w : κ → ℝ := fun j => c j / C
    let u : κ → ℝ := fun j => y j * t j / c j
    have hw_pos : ∀ j, 0 < w j := fun j => div_pos (hc j) hC_pos
    have hw_sum : ∑ j, w j = 1 := by
      dsimp [w]
      rw [← Finset.sum_div]
      exact div_self hC_pos.ne'
    have hu_pos : ∀ j, 0 < u j := fun j => div_pos (mul_pos (hy j) (ht_pos j)) (hc j)
    have hamgm := weighted_am_gm w u hw_pos hw_sum hu_pos
    have hwu_sum : ∑ j, w j * u j = (∑ j, y j * t j) / C := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp [w, u]
      have hcj : c j ≠ 0 := (hc j).ne'
      field_simp [hcj]
    have hwu_prod : ∏ j, u j ^ w j =
        (∏ j, y j ^ (c j / C)) / (∏ j, (colNorm A c x j) ^ (c j / C)) := by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      dsimp [u, w, colNorm]
      have hy_div : y j * t j / c j = y j / (c j / t j) := by
        have hcj : c j ≠ 0 := (hc j).ne'
        have htj : t j ≠ 0 := (ht_pos j).ne'
        field_simp [hcj, htj]
      rw [hy_div, Real.div_rpow (hy j).le (div_pos (hc j) (ht_pos j)).le]
    rw [hwu_sum, hwu_prod] at hamgm
    unfold kappa
    change (∑ i, ∑ j, A i j * x i * colNorm A c x j) /
        ((∏ i, x i ^ (r i / R)) * ∏ j, colNorm A c x j ^ (c j / C)) ≤
      (∑ i, ∑ j, A i j * x i * y j) /
        ((∏ i, x i ^ (r i / R)) * ∏ j, y j ^ (c j / C))
    rw [hnum_col, hnum_xy]
    rw [div_le_div_iff₀ (mul_pos hpx_pos hpc_pos) (mul_pos hpx_pos hpy_pos)]
    rw [div_le_div_iff₀ hpc_pos hC_pos] at hamgm
    nlinarith [hpx_pos]
