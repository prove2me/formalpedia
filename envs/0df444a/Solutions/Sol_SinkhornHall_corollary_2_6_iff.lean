-- Prove2me | solution 1 for SinkhornHall.corollary_2_6_iff
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T00:13:43.725203+00:00
-- url     : https://prove2.me/submissions/6912c757-e5ad-4c93-983b-bfde934e95cc

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis
import Theorems.Thm_SinkhornHall_theorem_2_3_2
import Theorems.Thm_SinkhornHall_corollary_2_6_edge

open Finset SinkhornHall

theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j)
    (h2 : 1 < numEdges A)
    (r : ι → ℝ) (c : κ → ℝ) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hRC : ∑ i, r i = ∑ j, c j) :
    ¬ ApproxScalable A r c ↔
      ∃ (x : ι → ℝ) (y : κ → ℝ), (∀ i, 0 < x i) ∧ (∀ j, 0 < y j) ∧
        kappa A r c x y ≤ Amin A := by
  classical
  let E : Finset (ι × κ) := Finset.univ.filter (fun p : ι × κ => 0 < A p.1 p.2)
  have hE_card : E.card = numEdges A := by
    unfold numEdges
    congr 1
  have hE_ne : E.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨⟨i₀, j₀⟩, hp₀⟩ := id hE_ne
  have hj₀ : 0 < A i₀ j₀ := (Finset.mem_filter.mp hp₀).2
  have hne_ι : Nonempty ι := ⟨i₀⟩
  have hne_κ : Nonempty κ := ⟨j₀⟩
  have hAmin_pos : 0 < Amin A := by
    let m0 : ℝ := E.inf' hE_ne (fun p => A p.1 p.2)
    have hm0_pos : 0 < m0 :=
      (Finset.lt_inf'_iff hE_ne).mpr fun p hp => (Finset.mem_filter.mp hp).2
    have hm0_le : m0 ≤ Amin A := by
      refine le_csInf ⟨A i₀ j₀, i₀, j₀, hj₀, rfl⟩ ?_
      rintro a ⟨i, j, hpos, rfl⟩
      exact Finset.inf'_le (fun p : ι × κ => A p.1 p.2)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ (i, j), hpos⟩)
    exact hm0_pos.trans_le hm0_le
  constructor
  · intro hnot
    have hnot2 := (theorem_2_3_2 A hA hrow hcol r c hr hc hRC).not.mp hnot
    push Not at hnot2
    obtain ⟨x, y, hx, hy, hlt⟩ := hnot2 (Amin A) hAmin_pos
    exact ⟨x, y, hx, hy, hlt.le⟩
  · rintro ⟨x, y, hx, hy, hκ⟩ happrox
    have hedge := corollary_2_6_edge A hA hrow hcol h2 r c hr hc hRC x y hx hy hκ
    let R : ℝ := ∑ i, r i
    let C : ℝ := ∑ j, c j
    have hR_pos : 0 < R := Finset.sum_pos (fun i _ => hr i) Finset.univ_nonempty
    let Dx : ℝ := ∏ i, x i ^ (r i / R)
    let Dy : ℝ := ∏ j, y j ^ (c j / C)
    have hDx_pos : 0 < Dx := Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx i) _
    have hDy_pos : 0 < Dy := Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hy j) _
    let D : ℝ := Dx * Dy
    let a : ι → ℝ := fun i => Real.log (x i)
    let b : κ → ℝ := fun j => Real.log (y j)
    let d : ℝ := Real.log D
    have hRd : R * d = (∑ i, r i * a i) + ∑ j, c j * b j := by
      have hlog_D : d = Real.log Dx + Real.log Dy := Real.log_mul hDx_pos.ne' hDy_pos.ne'
      have hlog_Dx : Real.log Dx = (∑ i, r i * a i) / R := by
        dsimp [Dx, a]
        rw [Real.log_prod fun i _ => (Real.rpow_pos_of_pos (hx i) _).ne', Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Real.log_rpow (hx i)]
        ring
      have hlog_Dy : Real.log Dy = (∑ j, c j * b j) / R := by
        dsimp [Dy, b]
        rw [Real.log_prod fun j _ => (Real.rpow_pos_of_pos (hy j) _).ne', Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Real.log_rpow (hy j)]
        dsimp [R, C]
        rw [hRC]
        ring
      rw [hlog_D, hlog_Dx, hlog_Dy]
      have hRne : R ≠ 0 := hR_pos.ne'
      field_simp [hRne]
    have hgap_edge : ∀ p ∈ E, 0 < d - (a p.1 + b p.2) := by
      intro p hp
      have hpos : 0 < A p.1 p.2 := (Finset.mem_filter.mp hp).2
      have hlt : x p.1 * y p.2 < D := hedge p.1 p.2 hpos
      have hlog_lt := Real.log_lt_log (mul_pos (hx p.1) (hy p.2)) hlt
      rw [Real.log_mul (hx p.1).ne' (hy p.2).ne'] at hlog_lt
      dsimp [a, b, d]
      linarith
    let γ : ℝ := E.inf' hE_ne (fun p => d - (a p.1 + b p.2))
    have hγ_pos : 0 < γ := (Finset.lt_inf'_iff hE_ne).mpr hgap_edge
    let Ma : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i : ι => |a i|)
    let Mb : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun j : κ => |b j|)
    let K : ℝ := 1 + |d| + Ma + Mb
    have hMa_nn : 0 ≤ Ma :=
      (abs_nonneg (a i₀)).trans (Finset.le_sup' (fun i : ι => |a i|) (Finset.mem_univ i₀))
    have hMb_nn : 0 ≤ Mb :=
      (abs_nonneg (b j₀)).trans (Finset.le_sup' (fun j : κ => |b j|) (Finset.mem_univ j₀))
    have hK_pos : 0 < K := by dsimp [K]; linarith [abs_nonneg d]
    let ε : ℝ := min (R / 2) (γ * R / (4 * K))
    have hε_pos : 0 < ε :=
      lt_min (half_pos hR_pos) (div_pos (mul_pos hγ_pos hR_pos) (mul_pos (by norm_num) hK_pos))
    obtain ⟨x', y', hx', hy', herr⟩ := happrox ε hε_pos
    let B' : ι × κ → ℝ := fun p => A p.1 p.2 * x' p.1 * y' p.2
    have hB'_nn : ∀ p, 0 ≤ B' p :=
      fun p => mul_nonneg (mul_nonneg (hA p.1 p.2) (hx' p.1).le) (hy' p.2).le
    have hpt_gap : ∀ p : ι × κ, γ * B' p ≤ B' p * (d - a p.1 - b p.2) := by
      intro p
      by_cases hpE : p ∈ E
      · have hle : γ ≤ d - (a p.1 + b p.2) :=
          Finset.inf'_le (fun q : ι × κ => d - (a q.1 + b q.2)) hpE
        have heq : d - (a p.1 + b p.2) = d - a p.1 - b p.2 := by ring
        rw [← heq, mul_comm (B' p)]
        exact mul_le_mul_of_nonneg_right hle (hB'_nn p)
      · have hnot : ¬ 0 < A p.1 p.2 := by
          intro hpos
          exact hpE (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpos⟩)
        have hA0 : A p.1 p.2 = 0 := le_antisymm (not_lt.mp hnot) (hA p.1 p.2)
        have hB'0 : B' p = 0 := by simp [B', hA0]
        simp [hB'0]
    let SB' : ℝ := ∑ i, ∑ j, B' (i, j)
    have hsum_gap : γ * SB' ≤
        (SB' - R) * d - (∑ i, ((∑ j, B' (i, j)) - r i) * a i) -
          ∑ j, ((∑ i, B' (i, j)) - c j) * b j := by
      have h1 : γ * SB' ≤ ∑ p : ι × κ, B' p * (d - a p.1 - b p.2) := by
        have hS : SB' = ∑ p : ι × κ, B' p := (Fintype.sum_prod_type (f := B')).symm
        rw [hS, Finset.mul_sum]
        exact Finset.sum_le_sum fun p _ => hpt_gap p
      have h2 : ∑ p : ι × κ, B' p * (d - a p.1 - b p.2) =
          SB' * d - (∑ i, (∑ j, B' (i, j)) * a i) - ∑ j, (∑ i, B' (i, j)) * b j := by
        rw [Fintype.sum_prod_type]
        have hexp : ∀ i j, B' (i, j) * (d - a i - b j) =
            B' (i, j) * d - B' (i, j) * a i - B' (i, j) * b j := fun i j => by ring
        simp_rw [hexp, Finset.sum_sub_distrib]
        congr 1
        · congr 1
          · simp only [SB', ← Finset.sum_mul]
          · exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
        · rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
      have h3 : SB' * d - (∑ i, (∑ j, B' (i, j)) * a i) - ∑ j, (∑ i, B' (i, j)) * b j =
          (SB' - R) * d - (∑ i, ((∑ j, B' (i, j)) - r i) * a i) -
            ∑ j, ((∑ i, B' (i, j)) - c j) * b j := by
        simp only [sub_mul, Finset.sum_sub_distrib]
        linarith [hRd]
      linarith
    let Er : ℝ := ∑ i, |(∑ j, B' (i, j)) - r i|
    let Ec : ℝ := ∑ j, |(∑ i, B' (i, j)) - c j|
    have hEr_nn : 0 ≤ Er := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hEc_nn : 0 ≤ Ec := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hErr_lt : Er + Ec < ε := herr
    have hS_diff : |SB' - R| ≤ Er := by
      have h1 : SB' - R = ∑ i, ((∑ j, B' (i, j)) - r i) := by
        dsimp [SB', R]
        rw [Finset.sum_sub_distrib]
      rw [h1]
      exact Finset.abs_sum_le_sum_abs _ _
    have hSB'_lb : R / 2 ≤ SB' := by
      have hε1 : ε ≤ R / 2 := min_le_left _ _
      have habs := neg_le_of_abs_le hS_diff
      linarith
    have hterm_d : (SB' - R) * d ≤ |d| * Er := by
      calc (SB' - R) * d
          ≤ |(SB' - R) * d| := le_abs_self _
        _ = |d| * |SB' - R| := by rw [abs_mul, mul_comm]
        _ ≤ |d| * Er := mul_le_mul_of_nonneg_left hS_diff (abs_nonneg d)
    have hterm_a : -(∑ i, ((∑ j, B' (i, j)) - r i) * a i) ≤ Ma * Er := by
      calc -(∑ i, ((∑ j, B' (i, j)) - r i) * a i)
          ≤ |∑ i, ((∑ j, B' (i, j)) - r i) * a i| := neg_le_abs _
        _ ≤ ∑ i, |((∑ j, B' (i, j)) - r i) * a i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, |(∑ j, B' (i, j)) - r i| * Ma := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left
              (Finset.le_sup' (fun k : ι => |a k|) (Finset.mem_univ i)) (abs_nonneg _)
        _ = Ma * Er := by rw [← Finset.sum_mul, mul_comm]
    have hterm_b : -(∑ j, ((∑ i, B' (i, j)) - c j) * b j) ≤ Mb * Ec := by
      calc -(∑ j, ((∑ i, B' (i, j)) - c j) * b j)
          ≤ |∑ j, ((∑ i, B' (i, j)) - c j) * b j| := neg_le_abs _
        _ ≤ ∑ j, |((∑ i, B' (i, j)) - c j) * b j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, |(∑ i, B' (i, j)) - c j| * Mb := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left
              (Finset.le_sup' (fun l : κ => |b l|) (Finset.mem_univ j)) (abs_nonneg _)
        _ = Mb * Ec := by rw [← Finset.sum_mul, mul_comm]
    have hRHS_ub : (SB' - R) * d - (∑ i, ((∑ j, B' (i, j)) - r i) * a i) -
        ∑ j, ((∑ i, B' (i, j)) - c j) * b j ≤ K * ε := by
      have h1 : |d| * Er + Ma * Er + Mb * Ec ≤ K * (Er + Ec) := by
        dsimp [K]
        nlinarith [abs_nonneg d, hMa_nn, hMb_nn, hEr_nn, hEc_nn]
      have h2 : K * (Er + Ec) < K * ε := mul_lt_mul_of_pos_left hErr_lt hK_pos
      linarith
    have hLHS_lb : γ * (R / 2) ≤ γ * SB' :=
      mul_le_mul_of_nonneg_left hSB'_lb hγ_pos.le
    have hε2 : K * ε ≤ γ * R / 4 := by
      have hmin : ε ≤ γ * R / (4 * K) := min_le_right _ _
      have hm := mul_le_mul_of_nonneg_left hmin hK_pos.le
      have hKne : K ≠ 0 := hK_pos.ne'
      have hrew : K * (γ * R / (4 * K)) = γ * R / 4 := by field_simp [hKne]
      rwa [hrew] at hm
    have hγR_pos : 0 < γ * R := mul_pos hγ_pos hR_pos
    linarith
