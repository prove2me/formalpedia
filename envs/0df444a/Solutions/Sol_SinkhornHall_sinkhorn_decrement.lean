-- Prove2me | solution 1 for SinkhornHall.sinkhorn_decrement
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T00:09:57.003614+00:00
-- url     : https://prove2.me/submissions/623f98c1-730e-4b5e-8262-8c903501d3e2

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis
import Theorems.Thm_FamousTheorems_all_card_le_biunion_card_iff_exists_injective
import Theorems.Thm_SinkhornHall_lemma_2_2
import Theorems.Thm_SinkhornHall_lemma_1_1
import Theorems.Thm_SinkhornHall_lemma_2_4

open Finset SinkhornHall

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j) (hpm : ¬ HasPerfectMatching A)
    (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    let y := colNorm A 1 x
    let x' := rowNorm A 1 y
    let y' := colNorm A 1 x'
    Real.log (kappa A 1 1 x' y') - Real.log (kappa A 1 1 x y) ≤ -4 / (n : ℝ) ^ 2 := by
  intro y x' y'
  have hn_pos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exfalso
      exact hpm ⟨Equiv.refl (Fin 0), fun i => i.elim0⟩
    · exact hpos
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn_pos
  have hn_pos_real : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  let t : Fin n → Finset (Fin n) := fun i => Finset.univ.filter (fun j => 0 < A i j)
  have hbiu : ∀ s : Finset (Fin n), s.biUnion t = Gamma A s := by
    intro s
    ext j
    simp [t, Gamma]
  have hnot_hall : ¬ ∀ s : Finset (Fin n), s.card ≤ (s.biUnion t).card := by
    intro hall
    obtain ⟨f, hfinj, hft⟩ :=
      (FamousTheorems.all_card_le_biunion_card_iff_exists_injective t).mp hall
    have hfbij : Function.Bijective f := Finite.injective_iff_bijective.mp hfinj
    refine hpm ⟨Equiv.ofBijective f hfbij, fun i => ?_⟩
    have hmem := hft i
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem
  push Not at hnot_hall
  obtain ⟨X, hX_lt⟩ := hnot_hall
  rw [hbiu X] at hX_lt
  let Y : Finset (Fin n) := (Gamma A X)ᶜ
  have hXY_stable : IsStable A X Y := by
    intro i hi j hj hpos
    have hjG : j ∈ Gamma A X := by
      simp only [Gamma, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, hi, hpos⟩
    exact (Finset.mem_compl.mp hj) hjG
  have hXY_lb : (2 : ℝ) ≤
      2 * (∑ _ ∈ X, (1 : ℝ)) + 2 * (∑ _ ∈ Y, (1 : ℝ)) -
        (∑ _ : Fin n, (1 : ℝ)) - (∑ _ : Fin n, (1 : ℝ)) := by
    have hcard_le : (Gamma A X).card + 1 ≤ X.card := Nat.succ_le_of_lt hX_lt
    have hcard_real : ((Gamma A X).card : ℝ) + 1 ≤ (X.card : ℝ) := by exact_mod_cast hcard_le
    have hcompl_sum : (∑ _ ∈ Y, (1 : ℝ)) + (∑ _ ∈ Gamma A X, (1 : ℝ)) = ∑ _ : Fin n, (1 : ℝ) := by
      have := Finset.sum_add_sum_compl Y (fun _ : Fin n => (1 : ℝ))
      rwa [compl_compl] at this
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin] at hcompl_sum ⊢
    linarith
  have hy_pos : ∀ j, 0 < y j := by
    intro j
    obtain ⟨i₀, hi₀⟩ := hcol j
    have ht_pos : 0 < ∑ i, A i j * x i :=
      (mul_pos hi₀ (hx i₀)).trans_le
        (Finset.single_le_sum (f := fun i => A i j * x i)
          (fun i _ => mul_nonneg (hA i j) (hx i).le) (Finset.mem_univ i₀))
    exact div_pos zero_lt_one ht_pos
  have hx'_pos : ∀ i, 0 < x' i := by
    intro i
    obtain ⟨j₀, hj₀⟩ := hrow i
    have hs_pos : 0 < ∑ j, A i j * y j :=
      (mul_pos hj₀ (hy_pos j₀)).trans_le
        (Finset.single_le_sum (f := fun j => A i j * y j)
          (fun j _ => mul_nonneg (hA i j) (hy_pos j).le) (Finset.mem_univ j₀))
    exact div_pos zero_lt_one hs_pos
  let oneVec : Fin n → ℝ := 1
  have hone_pos : ∀ i : Fin n, 0 < oneVec i := fun _ => zero_lt_one
  let p : Fin n → ℝ := fun i => ∑ j, A i j * x i * y j
  let q : Fin n → ℝ := fun j => ∑ i, A i j * x' i * y j
  have hp_pos : ∀ i, 0 < p i := by
    intro i
    obtain ⟨j₀, hj₀⟩ := hrow i
    exact (mul_pos (mul_pos hj₀ (hx i)) (hy_pos j₀)).trans_le
      (Finset.single_le_sum (f := fun j => A i j * x i * y j)
        (fun j _ => mul_nonneg (mul_nonneg (hA i j) (hx i).le) (hy_pos j).le)
        (Finset.mem_univ j₀))
  have hq_pos : ∀ j, 0 < q j := by
    intro j
    obtain ⟨i₀, hi₀⟩ := hcol j
    exact (mul_pos (mul_pos hi₀ (hx'_pos i₀)) (hy_pos j)).trans_le
      (Finset.single_le_sum (f := fun i => A i j * x' i * y j)
        (fun i _ => mul_nonneg (mul_nonneg (hA i j) (hx'_pos i).le) (hy_pos j).le)
        (Finset.mem_univ i₀))
  have hcol_xy : ∀ j, ∑ i, A i j * x i * y j = 1 := by
    intro j
    obtain ⟨i₀, hi₀⟩ := hcol j
    have ht_pos : 0 < ∑ i, A i j * x i :=
      (mul_pos hi₀ (hx i₀)).trans_le
        (Finset.single_le_sum (f := fun i => A i j * x i)
          (fun i _ => mul_nonneg (hA i j) (hx i).le) (Finset.mem_univ i₀))
    have hmul : ∑ i, A i j * x i * y j = (∑ i, A i j * x i) * y j := by
      rw [Finset.sum_mul]
    rw [hmul]
    dsimp [y, colNorm]
    exact mul_div_cancel₀ 1 ht_pos.ne'
  have hrow_x'y : ∀ i, ∑ j, A i j * x' i * y j = 1 := by
    intro i
    obtain ⟨j₀, hj₀⟩ := hrow i
    have hs_pos : 0 < ∑ j, A i j * y j :=
      (mul_pos hj₀ (hy_pos j₀)).trans_le
        (Finset.single_le_sum (f := fun j => A i j * y j)
          (fun j _ => mul_nonneg (hA i j) (hy_pos j).le) (Finset.mem_univ j₀))
    have hmul : ∑ j, A i j * x' i * y j = x' i * ∑ j, A i j * y j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hmul]
    dsimp [x', rowNorm]
    exact div_mul_cancel₀ 1 hs_pos.ne'
  have hp_l1 : (2 : ℝ) ≤ ∑ i, |oneVec i - p i| := by
    have h22 := lemma_2_2 A hA hrow hcol oneVec oneVec hone_pos hone_pos x y hx hy_pos
      X Y hXY_stable
    have hcol0 : ∑ j, |(∑ i, A i j * x i * y j) - oneVec j| = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hcol_xy j]
      simp [oneVec]
    have hrow_eq : ∑ i, |(∑ j, A i j * x i * y j) - oneVec i| = ∑ i, |oneVec i - p i| :=
      Finset.sum_congr rfl fun i _ => abs_sub_comm (p i) (oneVec i)
    rw [hcol0, add_zero, hrow_eq] at h22
    exact hXY_lb.trans h22
  have hq_l1 : (2 : ℝ) ≤ ∑ j, |oneVec j - q j| := by
    have h22 := lemma_2_2 A hA hrow hcol oneVec oneVec hone_pos hone_pos x' y hx'_pos hy_pos
      X Y hXY_stable
    have hrow0 : ∑ i, |(∑ j, A i j * x' i * y j) - oneVec i| = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hrow_x'y i]
      simp [oneVec]
    have hcol_eq : ∑ j, |(∑ i, A i j * x' i * y j) - oneVec j| = ∑ j, |oneVec j - q j| :=
      Finset.sum_congr rfl fun j _ => abs_sub_comm (q j) (oneVec j)
    rw [hrow0, zero_add, hcol_eq] at h22
    exact hXY_lb.trans h22
  have hp_sum : ∑ i, oneVec i = ∑ i, p i := by
    dsimp [p, oneVec]
    rw [Finset.sum_comm]
    simp_rw [hcol_xy]
  have hq_sum : ∑ j, oneVec j = ∑ j, q j := by
    dsimp [q, oneVec]
    rw [Finset.sum_comm]
    simp_rw [hrow_x'y]
  have hno_p : ¬ ∃ i, p i = 0 ∧ 0 < oneVec i := by
    rintro ⟨i, hp0, _⟩
    exact (hp_pos i).ne' hp0
  have hno_q : ¬ ∃ j, q j = 0 ∧ 0 < oneVec j := by
    rintro ⟨j, hq0, _⟩
    exact (hq_pos j).ne' hq0
  have hsum_one : ∑ i : Fin n, oneVec i = (n : ℝ) := by
    simp [oneVec]
  have hkl_p : (2 : ℝ) / n ≤ ∑ i, oneVec i * Real.log (oneVec i / p i) := by
    have hp11 := lemma_1_1 oneVec p (fun _ => zero_le_one) (fun i => (hp_pos i).le) hp_sum
    rw [klDiv, if_neg hno_p, EReal.coe_le_coe_iff, hsum_one] at hp11
    have hsq : (4 : ℝ) ≤ (∑ i, |oneVec i - p i|) ^ 2 := by nlinarith [hp_l1]
    have hdiv : (2 : ℝ) / n ≤ (∑ i, |oneVec i - p i|) ^ 2 / (2 * (n : ℝ)) := by
      rw [div_le_div_iff₀ hn_pos_real (by linarith)]
      nlinarith
    exact hdiv.trans hp11
  have hkl_q : (2 : ℝ) / n ≤ ∑ j, oneVec j * Real.log (oneVec j / q j) := by
    have hq11 := lemma_1_1 oneVec q (fun _ => zero_le_one) (fun j => (hq_pos j).le) hq_sum
    rw [klDiv, if_neg hno_q, EReal.coe_le_coe_iff, hsum_one] at hq11
    have hsq : (4 : ℝ) ≤ (∑ j, |oneVec j - q j|) ^ 2 := by nlinarith [hq_l1]
    have hdiv : (2 : ℝ) / n ≤ (∑ j, |oneVec j - q j|) ^ 2 / (2 * (n : ℝ)) := by
      rw [div_le_div_iff₀ hn_pos_real (by linarith)]
      nlinarith
    exact hdiv.trans hq11
  have h24 := lemma_2_4 A hA hrow hcol oneVec oneVec hone_pos hone_pos rfl x hx
  dsimp only [oneVec] at h24 hno_p hno_q hkl_p hkl_q
  change ((Real.log (kappa A 1 1 x' y') - Real.log (kappa A 1 1 x y) : ℝ) : EReal) =
    -(klDiv 1 p) / ((∑ _ : Fin n, (1 : ℝ) : ℝ) : EReal) -
      klDiv 1 q / ((∑ _ : Fin n, (1 : ℝ) : ℝ) : EReal) at h24
  rw [klDiv, if_neg hno_p, klDiv, if_neg hno_q] at h24
  have hsum1 : (∑ _ : Fin n, (1 : ℝ)) = (n : ℝ) := by simp
  rw [hsum1] at h24
  have hreal_eq : Real.log (kappa A 1 1 x' y') - Real.log (kappa A 1 1 x y) =
      -(∑ i, (1 : Fin n → ℝ) i * Real.log ((1 : Fin n → ℝ) i / p i)) / (n : ℝ) -
        (∑ j, (1 : Fin n → ℝ) j * Real.log ((1 : Fin n → ℝ) j / q j)) / (n : ℝ) :=
    EReal.coe_eq_coe_iff.mp h24
  rw [hreal_eq, neg_div]
  have hdiv_p : (2 / (n : ℝ)) / (n : ℝ) ≤
      (∑ i, (1 : Fin n → ℝ) i * Real.log ((1 : Fin n → ℝ) i / p i)) / (n : ℝ) :=
    div_le_div_of_nonneg_right hkl_p hn_pos_real.le
  have hdiv_q : (2 / (n : ℝ)) / (n : ℝ) ≤
      (∑ j, (1 : Fin n → ℝ) j * Real.log ((1 : Fin n → ℝ) j / q j)) / (n : ℝ) :=
    div_le_div_of_nonneg_right hkl_q hn_pos_real.le
  have h4 : -((2 / (n : ℝ)) / (n : ℝ)) - (2 / (n : ℝ)) / (n : ℝ) = -4 / (n : ℝ) ^ 2 := by
    have hne : (n : ℝ) ≠ 0 := hn_pos_real.ne'
    field_simp [hne]
    ring
  linarith
