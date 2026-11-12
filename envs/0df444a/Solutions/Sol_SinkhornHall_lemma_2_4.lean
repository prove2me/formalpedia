-- Prove2me | solution 1 for SinkhornHall.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T23:58:05.43207+00:00
-- url     : https://prove2.me/submissions/a0208f2f-24e9-424b-a46a-f81049cc5330

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis

open Finset SinkhornHall

theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι]
    (A : Matrix ι κ ℝ) (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∃ j, 0 < A i j)
    (hcol : ∀ j, ∃ i, 0 < A i j)
    (r : ι → ℝ) (c : κ → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hRC : ∑ i, r i = ∑ j, c j) (x : ι → ℝ) (hx : ∀ i, 0 < x i) :
    let y := colNorm A c x
    let x' := rowNorm A r y
    let y' := colNorm A c x'
    let p : ι → ℝ := fun i => ∑ j, A i j * x i * y j
    let q : κ → ℝ := fun j => ∑ i, A i j * x' i * y j
    ((Real.log (kappa A r c x' y') - Real.log (kappa A r c x y) : ℝ) : EReal) =
      -(klDiv r p) / ((∑ i, r i : ℝ) : EReal) - klDiv c q / ((∑ j, c j : ℝ) : EReal) := by
  intro y x' y' p q
  let _ := hRC
  have hne_κ : Nonempty κ := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    obtain ⟨j₀, _⟩ := hrow i₀
    exact ⟨j₀⟩
  let R : ℝ := ∑ i, r i
  let C : ℝ := ∑ j, c j
  have hR_pos : 0 < R := Finset.sum_pos (fun i _ => hr i) Finset.univ_nonempty
  have hC_pos : 0 < C := Finset.sum_pos (fun j _ => hc j) Finset.univ_nonempty
  let t1 : κ → ℝ := fun j => ∑ i, A i j * x i
  have ht1_pos : ∀ j, 0 < t1 j := by
    intro j
    obtain ⟨i₀, hi₀⟩ := hcol j
    exact (mul_pos hi₀ (hx i₀)).trans_le
      (Finset.single_le_sum (f := fun i => A i j * x i)
        (fun i _ => mul_nonneg (hA i j) (hx i).le) (Finset.mem_univ i₀))
  have hy_pos : ∀ j, 0 < y j := fun j => div_pos (hc j) (ht1_pos j)
  let s1 : ι → ℝ := fun i => ∑ j, A i j * y j
  have hs1_pos : ∀ i, 0 < s1 i := by
    intro i
    obtain ⟨j₀, hj₀⟩ := hrow i
    exact (mul_pos hj₀ (hy_pos j₀)).trans_le
      (Finset.single_le_sum (f := fun j => A i j * y j)
        (fun j _ => mul_nonneg (hA i j) (hy_pos j).le) (Finset.mem_univ j₀))
  have hx'_pos : ∀ i, 0 < x' i := fun i => div_pos (hr i) (hs1_pos i)
  let t2 : κ → ℝ := fun j => ∑ i, A i j * x' i
  have ht2_pos : ∀ j, 0 < t2 j := by
    intro j
    obtain ⟨i₀, hi₀⟩ := hcol j
    exact (mul_pos hi₀ (hx'_pos i₀)).trans_le
      (Finset.single_le_sum (f := fun i => A i j * x' i)
        (fun i _ => mul_nonneg (hA i j) (hx'_pos i).le) (Finset.mem_univ i₀))
  have hy'_pos : ∀ j, 0 < y' j := fun j => div_pos (hc j) (ht2_pos j)
  have hp_eq : ∀ i, p i = x i * s1 i := by
    intro i
    dsimp [p, s1]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hq_eq : ∀ j, q j = y j * t2 j := by
    intro j
    dsimp [q, t2]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hp_pos : ∀ i, 0 < p i := fun i => (hp_eq i).symm ▸ mul_pos (hx i) (hs1_pos i)
  have hq_pos : ∀ j, 0 < q j := fun j => (hq_eq j).symm ▸ mul_pos (hy_pos j) (ht2_pos j)
  have hnum_xy : ∑ i, ∑ j, A i j * x i * y j = C := by
    rw [Finset.sum_comm]
    have h1 : ∀ j, ∑ i, A i j * x i * y j = y j * t1 j := by
      intro j
      dsimp [t1]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [h1]
    dsimp [C, y, colNorm, t1]
    exact Finset.sum_congr rfl fun j _ => div_mul_cancel₀ (c j) (ht1_pos j).ne'
  have hnum_x'y' : ∑ i, ∑ j, A i j * x' i * y' j = C := by
    rw [Finset.sum_comm]
    have h1 : ∀ j, ∑ i, A i j * x' i * y' j = y' j * t2 j := by
      intro j
      dsimp [t2]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [h1]
    dsimp [C, y', colNorm, t2]
    exact Finset.sum_congr rfl fun j _ => div_mul_cancel₀ (c j) (ht2_pos j).ne'
  let Dx : ℝ := ∏ i, x i ^ (r i / R)
  let Dy : ℝ := ∏ j, y j ^ (c j / C)
  let Dx' : ℝ := ∏ i, x' i ^ (r i / R)
  let Dy' : ℝ := ∏ j, y' j ^ (c j / C)
  have hDx_pos : 0 < Dx := Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx i) _
  have hDy_pos : 0 < Dy := Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hy_pos j) _
  have hDx'_pos : 0 < Dx' := Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx'_pos i) _
  have hDy'_pos : 0 < Dy' := Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hy'_pos j) _
  have hlog_xy : Real.log (kappa A r c x y) = Real.log C - Real.log Dx - Real.log Dy := by
    have hk : kappa A r c x y = C / (Dx * Dy) := by
      unfold kappa
      dsimp [Dx, Dy, R, C]
      rw [hnum_xy]
    rw [hk, Real.log_div hC_pos.ne' (mul_pos hDx_pos hDy_pos).ne',
      Real.log_mul hDx_pos.ne' hDy_pos.ne']
    ring
  have hlog_x'y' : Real.log (kappa A r c x' y') = Real.log C - Real.log Dx' - Real.log Dy' := by
    have hk : kappa A r c x' y' = C / (Dx' * Dy') := by
      unfold kappa
      dsimp [Dx', Dy', R, C]
      rw [hnum_x'y']
    rw [hk, Real.log_div hC_pos.ne' (mul_pos hDx'_pos hDy'_pos).ne',
      Real.log_mul hDx'_pos.ne' hDy'_pos.ne']
    ring
  have hlog_Dx_diff : Real.log Dx' - Real.log Dx =
      (∑ i, r i * Real.log (r i / p i)) / R := by
    have h1 : Real.log Dx' = ∑ i, (r i / R) * Real.log (x' i) := by
      dsimp [Dx']
      rw [Real.log_prod fun i _ => (Real.rpow_pos_of_pos (hx'_pos i) _).ne']
      exact Finset.sum_congr rfl fun i _ => by rw [Real.log_rpow (hx'_pos i), mul_comm]
    have h2 : Real.log Dx = ∑ i, (r i / R) * Real.log (x i) := by
      dsimp [Dx]
      rw [Real.log_prod fun i _ => (Real.rpow_pos_of_pos (hx i) _).ne']
      exact Finset.sum_congr rfl fun i _ => by rw [Real.log_rpow (hx i), mul_comm]
    rw [h1, h2, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hratio : x' i / x i = r i / p i := by
      rw [hp_eq i]
      dsimp [x', rowNorm, s1]
      have hxne : x i ≠ 0 := (hx i).ne'
      have hsne : (∑ j, A i j * y j) ≠ 0 := (hs1_pos i).ne'
      field_simp [hxne, hsne]
    rw [← mul_sub, ← Real.log_div (hx'_pos i).ne' (hx i).ne', hratio, div_mul_eq_mul_div]
  have hlog_Dy_diff : Real.log Dy' - Real.log Dy =
      (∑ j, c j * Real.log (c j / q j)) / C := by
    have h1 : Real.log Dy' = ∑ j, (c j / C) * Real.log (y' j) := by
      dsimp [Dy']
      rw [Real.log_prod fun j _ => (Real.rpow_pos_of_pos (hy'_pos j) _).ne']
      exact Finset.sum_congr rfl fun j _ => by rw [Real.log_rpow (hy'_pos j), mul_comm]
    have h2 : Real.log Dy = ∑ j, (c j / C) * Real.log (y j) := by
      dsimp [Dy]
      rw [Real.log_prod fun j _ => (Real.rpow_pos_of_pos (hy_pos j) _).ne']
      exact Finset.sum_congr rfl fun j _ => by rw [Real.log_rpow (hy_pos j), mul_comm]
    rw [h1, h2, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hratio : y' j / y j = c j / q j := by
      rw [hq_eq j]
      dsimp [y', colNorm, t2]
      have hyne : y j ≠ 0 := (hy_pos j).ne'
      have htne : (∑ i, A i j * x' i) ≠ 0 := (ht2_pos j).ne'
      field_simp [hyne, htne]
    rw [← mul_sub, ← Real.log_div (hy'_pos j).ne' (hy_pos j).ne', hratio, div_mul_eq_mul_div]
  have hno_rp : ¬ ∃ i, p i = 0 ∧ 0 < r i := by
    rintro ⟨i, hp0, _⟩
    exact (hp_pos i).ne' hp0
  have hno_cq : ¬ ∃ j, q j = 0 ∧ 0 < c j := by
    rintro ⟨j, hq0, _⟩
    exact (hq_pos j).ne' hq0
  rw [klDiv, if_neg hno_rp, klDiv, if_neg hno_cq]
  have hreal : Real.log (kappa A r c x' y') - Real.log (kappa A r c x y) =
      -(∑ i, r i * Real.log (r i / p i)) / R - (∑ j, c j * Real.log (c j / q j)) / C := by
    rw [hlog_x'y', hlog_xy]
    have h1 := hlog_Dx_diff
    have h2 := hlog_Dy_diff
    have hRne : R ≠ 0 := hR_pos.ne'
    have hCne : C ≠ 0 := hC_pos.ne'
    calc (Real.log C - Real.log Dx' - Real.log Dy') - (Real.log C - Real.log Dx - Real.log Dy)
        = -(Real.log Dx' - Real.log Dx) - (Real.log Dy' - Real.log Dy) := by ring
      _ = -((∑ i, r i * Real.log (r i / p i)) / R) -
            (∑ j, c j * Real.log (c j / q j)) / C := by rw [h1, h2]
      _ = -(∑ i, r i * Real.log (r i / p i)) / R -
            (∑ j, c j * Real.log (c j / q j)) / C := by rw [neg_div]
  rw [hreal]
  rfl
