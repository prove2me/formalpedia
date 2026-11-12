-- Prove2me | solution 1 for SinkhornHall.log_kappa_sinkhorn_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T00:13:42.977282+00:00
-- url     : https://prove2.me/submissions/bef9cd0b-213c-42dc-b286-b76a99816e76

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis
import Theorems.Thm_SinkhornHall_kappa_normalization_optimal
import Theorems.Thm_SinkhornHall_sinkhorn_decrement

open Finset SinkhornHall

private lemma sinkhorn_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j) :
    ∀ ℓ : ℕ, (sinkhorn A ℓ).2 = colNorm A 1 (sinkhorn A ℓ).1 ∧
      (∀ i, 0 < (sinkhorn A ℓ).1 i) ∧ (∀ j, 0 < (sinkhorn A ℓ).2 j)
  | 0 => by
      refine ⟨rfl, fun _ => zero_lt_one, fun j => ?_⟩
      obtain ⟨i₀, hi₀⟩ := hcol j
      have ht_pos : 0 < ∑ i, A i j * (1 : Fin n → ℝ) i :=
        (mul_pos hi₀ zero_lt_one).trans_le
          (Finset.single_le_sum (f := fun i => A i j * (1 : Fin n → ℝ) i)
            (fun i _ => mul_nonneg (hA i j) zero_le_one) (Finset.mem_univ i₀))
      exact div_pos zero_lt_one ht_pos
  | ℓ + 1 => by
      obtain ⟨_, _, hy_pos⟩ := sinkhorn_inv A hA hrow hcol ℓ
      have hx'_pos : ∀ i, 0 < rowNorm A 1 (sinkhorn A ℓ).2 i := by
        intro i
        obtain ⟨j₀, hj₀⟩ := hrow i
        have hs_pos : 0 < ∑ j, A i j * (sinkhorn A ℓ).2 j :=
          (mul_pos hj₀ (hy_pos j₀)).trans_le
            (Finset.single_le_sum (f := fun j => A i j * (sinkhorn A ℓ).2 j)
              (fun j _ => mul_nonneg (hA i j) (hy_pos j).le) (Finset.mem_univ j₀))
        exact div_pos zero_lt_one hs_pos
      refine ⟨rfl, hx'_pos, fun j => ?_⟩
      obtain ⟨i₀, hi₀⟩ := hcol j
      have ht_pos : 0 < ∑ i, A i j * rowNorm A 1 (sinkhorn A ℓ).2 i :=
        (mul_pos hi₀ (hx'_pos i₀)).trans_le
          (Finset.single_le_sum (f := fun i => A i j * rowNorm A 1 (sinkhorn A ℓ).2 i)
            (fun i _ => mul_nonneg (hA i j) (hx'_pos i).le) (Finset.mem_univ i₀))
      exact div_pos zero_lt_one ht_pos

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j)
    (hpm : ¬ HasPerfectMatching A) :
    (∀ ℓ : ℕ, Real.log (kappa A 1 1 (sinkhorn A ℓ).1 (sinkhorn A ℓ).2) ≤
        Real.log ((numEdges A : ℝ) * Amax A) - 4 * (ℓ : ℝ) / (n : ℝ) ^ 2) ∧
      ∀ ℓ : ℕ, (1 / 4 : ℝ) * (n : ℝ) ^ 2 * Real.log ((numEdges A : ℝ) * Amax A / Amin A) ≤ ℓ →
        kappa A 1 1 (sinkhorn A ℓ).1 (sinkhorn A ℓ).2 ≤ Amin A := by
  have hn_pos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exfalso
      exact hpm ⟨Equiv.refl (Fin 0), fun i => i.elim0⟩
    · exact hpos
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn_pos
  obtain ⟨i₀⟩ := ‹Nonempty (Fin n)›
  obtain ⟨j₀, hj₀⟩ := hrow i₀
  have hn_pos_real : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have hn_sq_pos : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hn_pos_real
  have hκ_pos : ∀ (x y : Fin n → ℝ), (∀ i, 0 < x i) → (∀ j, 0 < y j) →
      0 < kappa A 1 1 x y := by
    intro x y hx hy
    have hnum_pos : 0 < ∑ i, ∑ j, A i j * x i * y j := by
      have hrow0 : 0 < ∑ j, A i₀ j * x i₀ * y j :=
        (mul_pos (mul_pos hj₀ (hx i₀)) (hy j₀)).trans_le
          (Finset.single_le_sum (f := fun j => A i₀ j * x i₀ * y j)
            (fun j _ => mul_nonneg (mul_nonneg (hA i₀ j) (hx i₀).le) (hy j).le)
            (Finset.mem_univ j₀))
      exact hrow0.trans_le
        (Finset.single_le_sum (f := fun i => ∑ j, A i j * x i * y j)
          (fun i _ => Finset.sum_nonneg fun j _ =>
            mul_nonneg (mul_nonneg (hA i j) (hx i).le) (hy j).le)
          (Finset.mem_univ i₀))
    have hden_pos : 0 < (∏ i, x i ^ ((1 : Fin n → ℝ) i / ∑ i', (1 : Fin n → ℝ) i')) *
        ∏ j, y j ^ ((1 : Fin n → ℝ) j / ∑ j', (1 : Fin n → ℝ) j') :=
      mul_pos (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx i) _)
        (Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hy j) _)
    exact div_pos hnum_pos hden_pos
  classical
  have hbdd_all : BddAbove {a : ℝ | ∃ i j, A i j = a} := by
    refine ⟨(Finset.univ : Finset (Fin n × Fin n)).sup' ⟨(i₀, j₀), Finset.mem_univ _⟩
      (fun p => A p.1 p.2), ?_⟩
    rintro a ⟨i, j, rfl⟩
    exact Finset.le_sup' (fun p : Fin n × Fin n => A p.1 p.2) (Finset.mem_univ (i, j))
  have hle_Amax : ∀ i j, A i j ≤ Amax A := fun i j => le_csSup hbdd_all ⟨i, j, rfl⟩
  have hAmax_pos : 0 < Amax A := hj₀.trans_le (hle_Amax i₀ j₀)
  let E : Finset (Fin n × Fin n) := Finset.univ.filter (fun p : Fin n × Fin n => 0 < A p.1 p.2)
  have hE_card : E.card = numEdges A := by
    unfold numEdges
    congr 1
  have hE_ne : E.Nonempty := ⟨(i₀, j₀), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj₀⟩⟩
  have hm_pos : 0 < (numEdges A : ℝ) := by
    rw [← hE_card]
    exact Nat.cast_pos.mpr hE_ne.card_pos
  have hmAmax_pos : 0 < (numEdges A : ℝ) * Amax A := mul_pos hm_pos hAmax_pos
  have hAmin_pos : 0 < Amin A := by
    let m0 : ℝ := E.inf' hE_ne (fun p => A p.1 p.2)
    have hm0_pos : 0 < m0 :=
      (Finset.lt_inf'_iff hE_ne).mpr fun p hp => (Finset.mem_filter.mp hp).2
    have hm0_le : m0 ≤ Amin A := by
      refine le_csInf ⟨A i₀ j₀, i₀, j₀, hj₀, rfl⟩ ?_
      rintro a ⟨i, j, hpos, rfl⟩
      exact Finset.inf'_le (fun p : Fin n × Fin n => A p.1 p.2)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ (i, j), hpos⟩)
    exact hm0_pos.trans_le hm0_le
  have hclause1 : ∀ ℓ : ℕ, Real.log (kappa A 1 1 (sinkhorn A ℓ).1 (sinkhorn A ℓ).2) ≤
      Real.log ((numEdges A : ℝ) * Amax A) - 4 * (ℓ : ℝ) / (n : ℝ) ^ 2 := by
    intro ℓ
    induction ℓ with
    | zero =>
        simp only [Nat.cast_zero, mul_zero, zero_div, sub_zero]
        have hopt := (kappa_normalization_optimal A hA hrow hcol 1 1
          (fun _ => zero_lt_one) (fun _ => zero_lt_one) rfl 1 1
          (fun _ => zero_lt_one) (fun _ => zero_lt_one)).2
        have hk11 : kappa A 1 1 1 1 ≤ (numEdges A : ℝ) * Amax A := by
          have h1 : kappa A 1 1 1 1 = ∑ p : Fin n × Fin n, A p.1 p.2 := by
            unfold kappa
            simp only [Pi.one_apply, Real.one_rpow, Finset.prod_const_one, mul_one, div_one]
            exact (Fintype.sum_prod_type (f := fun p : Fin n × Fin n => A p.1 p.2)).symm
          rw [h1]
          have hsplit : (∑ p : Fin n × Fin n, A p.1 p.2) = ∑ p ∈ E, A p.1 p.2 := by
            have hsp := Finset.sum_filter_add_sum_filter_not Finset.univ
              (fun p : Fin n × Fin n => 0 < A p.1 p.2) (fun p => A p.1 p.2)
            have hzero : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => ¬ 0 < A p.1 p.2),
                A p.1 p.2 = 0 := by
              refine Finset.sum_eq_zero fun p hp => ?_
              have hnot := (Finset.mem_filter.mp hp).2
              linarith [hA p.1 p.2]
            change (∑ p ∈ E, A p.1 p.2) + _ = _ at hsp
            linarith
          rw [hsplit, ← hE_card]
          calc ∑ p ∈ E, A p.1 p.2
              ≤ ∑ _ ∈ E, Amax A := Finset.sum_le_sum fun p _ => hle_Amax p.1 p.2
            _ = (E.card : ℝ) * Amax A := by simp
        have h0 := sinkhorn_inv A hA hrow hcol 0
        have hk0_pos := hκ_pos (sinkhorn A 0).1 (sinkhorn A 0).2 h0.2.1 h0.2.2
        exact Real.log_le_log hk0_pos (hopt.trans hk11)
    | succ ℓ ih =>
        obtain ⟨hy_eq, hx_pos, _⟩ := sinkhorn_inv A hA hrow hcol ℓ
        have hdec := sinkhorn_decrement A hA hrow hcol hpm (sinkhorn A ℓ).1 hx_pos
        dsimp only at hdec
        rw [← hy_eq] at hdec
        have hstep : sinkhorn A (ℓ + 1) =
            (rowNorm A 1 (sinkhorn A ℓ).2, colNorm A 1 (rowNorm A 1 (sinkhorn A ℓ).2)) := rfl
        rw [hstep]
        dsimp only
        push_cast
        have hlin : (Real.log ((numEdges A : ℝ) * Amax A) - 4 * (ℓ : ℝ) / (n : ℝ) ^ 2) +
            (-4 / (n : ℝ) ^ 2) =
            Real.log ((numEdges A : ℝ) * Amax A) - 4 * ((ℓ : ℝ) + 1) / (n : ℝ) ^ 2 := by ring
        linarith
  refine ⟨hclause1, fun ℓ hℓ => ?_⟩
  have h1 := hclause1 ℓ
  have hmul_le : Real.log ((numEdges A : ℝ) * Amax A / Amin A) ≤ 4 * (ℓ : ℝ) / (n : ℝ) ^ 2 := by
    rw [le_div_iff₀ hn_sq_pos]
    linarith
  rw [Real.log_div hmAmax_pos.ne' hAmin_pos.ne'] at hmul_le
  have hlog_le : Real.log (kappa A 1 1 (sinkhorn A ℓ).1 (sinkhorn A ℓ).2) ≤ Real.log (Amin A) := by
    linarith
  obtain ⟨_, hx_pos, hy_pos⟩ := sinkhorn_inv A hA hrow hcol ℓ
  exact (Real.log_le_log_iff (hκ_pos _ _ hx_pos hy_pos) hAmin_pos).mp hlog_le
