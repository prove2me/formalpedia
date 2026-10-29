-- Prove2me | solution 1 for SkutellaCQP.NoRel.corollary_2_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T20:34:01.898071+00:00
-- url     : https://prove2.me/submissions/15bb3630-d394-4518-a862-ec5fdca29b2f

import Mathlib
import Definitions.Def_SkutellaCQP_NoRel_Setting

open SkutellaCQP.NoRel
open Finset Matrix

private lemma prec_irrefl {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (i : Fin m) (j : Fin n) : ¬ prec p w i j j := by
  intro h
  rcases h with h | ⟨_, h⟩
  · exact lt_irrefl _ h
  · exact lt_irrefl _ h

private lemma prec_asym {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (i : Fin m) {j k : Fin n} (h : prec p w i k j) : ¬ prec p w i j k := by
  intro h'
  rcases h with h1 | ⟨h1, h2⟩ <;> rcases h' with h3 | ⟨h3, h4⟩
  · linarith
  · linarith
  · linarith
  · exact lt_asymm h2 h4

private lemma Dmat_same_machine {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (i : Fin m) (j k : Fin n) :
    Dmat p w (i, j) (i, k) =
      (if prec p w i k j then w j * p i k else 0) +
        (if prec p w i j k then w k * p i j else 0) := by
  unfold Dmat
  simp only [ne_eq, not_true_eq_false, false_or]
  by_cases hjk : j = k
  · subst hjk
    simp [prec_irrefl]
  · simp only [hjk, ↓reduceIte]
    by_cases h1 : prec p w i k j
    · have h2 : ¬ prec p w i j k := prec_asym p w i h1
      simp [h1, h2]
    · simp [h1]

private lemma lemma_2_2_aux {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (μ : (Fin n → Fin m) → ℝ) (j : Fin n) :
    E μ (fun σ => SkutellaCQP.NoRel.compl p w σ j) =
      ∑ i, ((∑ σ ∈ univ.filter (fun σ : Fin n → Fin m => σ j = i), μ σ) * p i j +
        ∑ k ∈ univ.filter (fun k => prec p w i k j),
          (∑ σ ∈ univ.filter (fun σ : Fin n → Fin m => σ j = i ∧ σ k = i), μ σ) * p i k) := by
  dsimp only [E, SkutellaCQP.NoRel.compl]
  have h1 :
      (∑ σ : Fin n → Fin m,
          μ σ * (p (σ j) j + ∑ k ∈ univ.filter (fun k => prec p w (σ j) k j ∧ σ k = σ j), p (σ j) k)) =
        ∑ σ : Fin n → Fin m, ∑ i : Fin m,
          if σ j = i then
            μ σ * (p i j + ∑ k ∈ univ.filter (fun k => prec p w i k j), if σ k = i then p i k else 0)
          else 0 := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_ite_eq univ (σ j)]
    simp only [Finset.mem_univ, ↓reduceIte]
    congr 2
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : prec p w (σ j) k j <;> by_cases h2 : σ k = σ j <;> simp [h1, h2]
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 :
      (∑ σ : Fin n → Fin m,
          if σ j = i then
            μ σ * (p i j + ∑ k ∈ univ.filter (fun k => prec p w i k j), if σ k = i then p i k else 0)
          else 0) =
        (∑ σ : Fin n → Fin m, if σ j = i then μ σ * p i j else 0) +
          ∑ σ : Fin n → Fin m,
            ∑ k ∈ univ.filter (fun k => prec p w i k j),
              if σ j = i ∧ σ k = i then μ σ * p i k else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases hσj : σ j = i
    · simp only [hσj, ↓reduceIte, true_and, mul_add, Finset.mul_sum, mul_ite, mul_zero]
    · simp only [hσj, ↓reduceIte, false_and, Finset.sum_const_zero, add_zero]
  rw [h2]
  congr 1
  · rw [← Finset.sum_filter, Finset.sum_mul]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_filter, Finset.sum_mul]

private lemma theorem_2_1_aux {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (a : Fin m → Fin n → ℝ)
    (μ : (Fin n → Fin m) → ℝ) (hμ : IsPairwiseRounding a μ) :
    E μ (SkutellaCQP.NoRel.val p w) = ZQP p w a := by
  have hE_val :
      E μ (SkutellaCQP.NoRel.val p w) =
        ∑ j, w j * E μ (fun σ => SkutellaCQP.NoRel.compl p w σ j) := by
    dsimp only [E, SkutellaCQP.NoRel.val]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun σ _ => by ring
  rw [hE_val]
  have hE_compl :
      ∀ j : Fin n,
        E μ (fun σ => SkutellaCQP.NoRel.compl p w σ j) =
          ∑ i : Fin m,
            (a i j * p i j +
              ∑ k ∈ univ.filter (fun k => prec p w i k j), a i j * a i k * p i k) := by
    intro j
    rw [lemma_2_2_aux]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hμ.2.2.1 j i]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_filter] at hk
    have hjk : j ≠ k := by
      rintro rfl
      exact prec_irrefl p w i j hk.2
    rw [hμ.2.2.2 j k hjk i i]
  simp_rw [hE_compl, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  unfold ZQP
  congr 1
  · dsimp only [cvec, SkutellaCQP.NoRel.vec, dotProduct]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun i _ => by ring
  · dsimp only [SkutellaCQP.NoRel.vec, dotProduct, Matrix.mulVec]
    simp_rw [Fintype.sum_prod_type]
    have hD :
        (∑ i : Fin m, ∑ j : Fin n,
            a i j * ∑ h : Fin m, ∑ k : Fin n, Dmat p w (i, j) (h, k) * a h k) =
          ∑ i : Fin m, ∑ j : Fin n,
            a i j * ∑ k : Fin n, Dmat p w (i, j) (i, k) * a i k := by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      rw [Finset.sum_eq_single i]
      · intro h _ hne
        refine Finset.sum_eq_zero fun k _ => ?_
        unfold Dmat
        simp [Ne.symm hne]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [hD]
    have hquad :
        ∀ i : Fin m,
          (∑ j : Fin n, a i j * ∑ k : Fin n, Dmat p w (i, j) (i, k) * a i k) =
            2 * ∑ j : Fin n, w j * ∑ k ∈ univ.filter (fun k => prec p w i k j),
              a i j * a i k * p i k := by
      intro i
      have lhs_eq :
          (∑ j : Fin n, a i j * ∑ k : Fin n, Dmat p w (i, j) (i, k) * a i k) =
            (∑ j : Fin n, ∑ k : Fin n,
                a i j * ((if prec p w i k j then w j * p i k else 0) * a i k)) +
              (∑ j : Fin n, ∑ k : Fin n,
                a i j * ((if prec p w i j k then w k * p i j else 0) * a i k)) := by
        simp_rw [Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Dmat_same_machine]
        ring
      rw [lhs_eq]
      have hswap :
          (∑ j : Fin n, ∑ k : Fin n,
              a i j * ((if prec p w i j k then w k * p i j else 0) * a i k)) =
            ∑ j : Fin n, ∑ k : Fin n,
              a i j * ((if prec p w i k j then w j * p i k else 0) * a i k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases h : prec p w i k j <;> simp [h] <;> ring
      rw [hswap, ← two_mul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases h : prec p w i k j <;> simp [h] <;> ring
    simp_rw [hquad]
    rw [← Finset.mul_sum, Finset.sum_comm]
    ring

private noncomputable def prodMeasure {m n : ℕ} (a : Fin m → Fin n → ℝ) (σ : Fin n → Fin m) : ℝ :=
  ∏ j : Fin n, a (σ j) j

private lemma isPairwiseRounding_prodMeasure {m n : ℕ} (a : Fin m → Fin n → ℝ) (ha : Feasible a) :
    IsPairwiseRounding a (prodMeasure a) := by
  refine ⟨fun σ => Finset.prod_nonneg fun j _ => ha.2 (σ j) j, ?_, fun j i => ?_, fun j k hjk i h => ?_⟩
  · unfold prodMeasure
    rw [← Fintype.prod_sum (fun j i => a i j)]
    simp [ha.1]
  · unfold prodMeasure
    rw [Finset.sum_filter]
    let b : Fin n → Fin m → ℝ := fun l r => if l = j then (if r = i then a i j else 0) else a r l
    have hterm :
        ∀ σ : Fin n → Fin m,
          (if σ j = i then ∏ l : Fin n, a (σ l) l else 0) = ∏ l : Fin n, b l (σ l) := by
      intro σ
      by_cases hσ : σ j = i
      · simp only [hσ, ↓reduceIte]
        refine Finset.prod_congr rfl fun l _ => ?_
        dsimp [b]
        by_cases hlj : l = j
        · subst hlj; simp [hσ]
        · simp [hlj]
      · simp only [hσ, ↓reduceIte]
        symm
        refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
        dsimp [b]
        simp [hσ]
    simp_rw [hterm, ← Fintype.prod_sum b]
    rw [Finset.prod_eq_single j]
    · dsimp [b]
      simp
    · intro l _ hlj
      dsimp [b]
      simp [hlj, ha.1 l]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · unfold prodMeasure
    rw [Finset.sum_filter]
    let b : Fin n → Fin m → ℝ := fun l r =>
      if l = j then (if r = i then a i j else 0)
      else if l = k then (if r = h then a h k else 0)
      else a r l
    have hterm :
        ∀ σ : Fin n → Fin m,
          (if σ j = i ∧ σ k = h then ∏ l : Fin n, a (σ l) l else 0) = ∏ l : Fin n, b l (σ l) := by
      intro σ
      by_cases hσ : σ j = i ∧ σ k = h
      · rcases hσ with ⟨hσj, hσk⟩
        simp only [hσj, hσk, and_self, ↓reduceIte]
        refine Finset.prod_congr rfl fun l _ => ?_
        dsimp [b]
        by_cases hlj : l = j
        · subst hlj; simp [hσj]
        · by_cases hlk : l = k
          · subst hlk; simp [hlj, hσk]
          · simp [hlj, hlk]
      · simp only [hσ, ↓reduceIte]
        symm
        by_cases hσj : σ j = i
        · have hσk : σ k ≠ h := fun h' => hσ ⟨hσj, h'⟩
          refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
          dsimp [b]
          simp [Ne.symm hjk, hσk]
        · refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
          dsimp [b]
          simp [hσj]
    simp_rw [hterm, ← Fintype.prod_sum b]
    rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ j)]
    have hk_mem : k ∈ univ.erase j := Finset.mem_erase.mpr ⟨Ne.symm hjk, Finset.mem_univ k⟩
    rw [← Finset.mul_prod_erase (univ.erase j) _ hk_mem]
    have hj_sum : (∑ r : Fin m, b j r) = a i j := by
      dsimp [b]; simp
    have hk_sum : (∑ r : Fin m, b k r) = a h k := by
      dsimp [b]; simp [Ne.symm hjk]
    have hrest : ∏ l ∈ (univ.erase j).erase k, ∑ r : Fin m, b l r = 1 := by
      refine Finset.prod_eq_one fun l hl => ?_
      rw [Finset.mem_erase] at hl
      have hlk : l ≠ k := hl.1
      have hlj : l ≠ j := (Finset.mem_erase.mp hl.2).1
      dsimp [b]
      simp [hlj, hlk, ha.1 l]
    rw [hj_sum, hk_sum, hrest, mul_one]

private lemma feasible_ind {m n : ℕ} (σ : Fin n → Fin m) : Feasible (ind σ) := by
  refine ⟨fun j => ?_, fun i j => ?_⟩
  · unfold ind; simp
  · unfold ind; split_ifs <;> linarith

private lemma isPairwiseRounding_ind {m n : ℕ} (σ : Fin n → Fin m) :
    IsPairwiseRounding (ind σ) (fun τ => if τ = σ then 1 else 0) := by
  refine ⟨fun τ => by dsimp; split_ifs <;> linarith, by simp, fun j i => ?_, fun j k _ i h => ?_⟩
  · rw [Finset.sum_filter]
    have :
        (∑ τ : Fin n → Fin m, if τ j = i then if τ = σ then (1 : ℝ) else 0 else 0) =
          ∑ τ : Fin n → Fin m, if τ = σ then (if σ j = i then 1 else 0) else 0 := by
      refine Finset.sum_congr rfl fun τ _ => ?_
      by_cases hτ : τ = σ
      · subst hτ; simp
      · simp [hτ]
    rw [this, Finset.sum_ite_eq' univ σ]
    simp [ind]
  · rw [Finset.sum_filter]
    have :
        (∑ τ : Fin n → Fin m, if τ j = i ∧ τ k = h then if τ = σ then (1 : ℝ) else 0 else 0) =
          ∑ τ : Fin n → Fin m, if τ = σ then (if σ j = i ∧ σ k = h then 1 else 0) else 0 := by
      refine Finset.sum_congr rfl fun τ _ => ?_
      by_cases hτ : τ = σ
      · subst hτ; simp
      · simp [hτ]
    rw [this, Finset.sum_ite_eq' univ σ]
    simp only [Finset.mem_univ, ↓reduceIte, ind]
    by_cases h1 : σ j = i <;> by_cases h2 : σ k = h <;> simp [h1, h2]

private lemma zqp_ind_eq_val {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (σ : Fin n → Fin m) : ZQP p w (ind σ) = SkutellaCQP.NoRel.val p w σ := by
  have h1 := theorem_2_1_aux p w (ind σ) (fun τ => if τ = σ then 1 else 0) (isPairwiseRounding_ind σ)
  have hE :
      E (fun τ => if τ = σ then 1 else 0) (SkutellaCQP.NoRel.val p w) =
        SkutellaCQP.NoRel.val p w σ := by
    dsimp only [E]; simp
  linarith

private lemma exists_pos_measure_le_expect {m n : ℕ}
    (μ : (Fin n → Fin m) → ℝ) (hμ0 : ∀ σ, 0 ≤ μ σ) (hμ1 : ∑ σ, μ σ = 1)
    (f : (Fin n → Fin m) → ℝ) :
    ∃ σ : Fin n → Fin m, 0 < μ σ ∧ f σ ≤ E μ f := by
  by_contra h
  push_neg at h
  have hlt : ∑ σ : Fin n → Fin m, μ σ * E μ f < ∑ σ : Fin n → Fin m, μ σ * f σ := by
    refine Finset.sum_lt_sum (fun σ _ => ?_) ?_
    · by_cases h0 : μ σ = 0
      · simp [h0]
      · have hpos : 0 < μ σ := lt_of_le_of_ne (hμ0 σ) (Ne.symm h0)
        exact mul_le_mul_of_nonneg_left (le_of_lt (h σ hpos)) (hμ0 σ)
    · have hex : ∃ σ ∈ (univ : Finset (Fin n → Fin m)), 0 < μ σ := by
        by_contra hall
        push_neg at hall
        have hzero : ∑ σ : Fin n → Fin m, μ σ = 0 :=
          Finset.sum_eq_zero fun σ hσ => le_antisymm (hall σ hσ) (hμ0 σ)
        linarith
      rcases hex with ⟨σ, hσ, hpos⟩
      exact ⟨σ, hσ, mul_lt_mul_of_pos_left (h σ hpos) hpos⟩
  rw [← Finset.sum_mul, hμ1, one_mul] at hlt
  exact lt_irrefl (E μ f) hlt

theorem solution {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) :
    ((∀ a : Fin m → Fin n → ℝ, Feasible a →
        ∃ σ : Fin n → Fin m, SkutellaCQP.NoRel.val p w σ ≤ ZQP p w a) ∧
      ∀ σ : Fin n → Fin m, ZQP p w (ind σ) = SkutellaCQP.NoRel.val p w σ) ∧
    ∀ a : Fin m → Fin n → ℝ, Feasible a →
      (∀ b : Fin m → Fin n → ℝ, Feasible b → ZQP p w a ≤ ZQP p w b) →
      ∀ σ : Fin n → Fin m, (∀ j, 0 < a (σ j) j) →
        ∀ τ : Fin n → Fin m, SkutellaCQP.NoRel.val p w σ ≤ SkutellaCQP.NoRel.val p w τ := by
  refine ⟨⟨?_, zqp_ind_eq_val p w⟩, ?_⟩
  · intro a ha
    have hμ := isPairwiseRounding_prodMeasure a ha
    have hE := theorem_2_1_aux p w a (prodMeasure a) hμ
    obtain ⟨σ, _, hle⟩ :=
      exists_pos_measure_le_expect (prodMeasure a) hμ.1 hμ.2.1 (SkutellaCQP.NoRel.val p w)
    exact ⟨σ, by linarith⟩
  · intro a ha hopt σ hσpos τ
    have hμ := isPairwiseRounding_prodMeasure a ha
    have hE := theorem_2_1_aux p w a (prodMeasure a) hμ
    have hval_ge : ∀ ρ : Fin n → Fin m, ZQP p w a ≤ SkutellaCQP.NoRel.val p w ρ := by
      intro ρ
      rw [← zqp_ind_eq_val p w ρ]
      exact hopt (ind ρ) (feasible_ind ρ)
    have hsum_zero :
        ∑ ρ : Fin n → Fin m, prodMeasure a ρ * (SkutellaCQP.NoRel.val p w ρ - ZQP p w a) = 0 := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hμ.2.1, one_mul]
      dsimp only [E] at hE
      linarith
    have hterm_zero :
        prodMeasure a σ * (SkutellaCQP.NoRel.val p w σ - ZQP p w a) = 0 := by
      have h_all := (Finset.sum_eq_zero_iff_of_nonneg (fun ρ _ =>
        mul_nonneg (hμ.1 ρ) (sub_nonneg.mpr (hval_ge ρ)))).mp hsum_zero
      exact h_all σ (Finset.mem_univ σ)
    have hμ_pos : 0 < prodMeasure a σ :=
      Finset.prod_pos fun j _ => hσpos j
    have h_eq : SkutellaCQP.NoRel.val p w σ = ZQP p w a := by
      rcases mul_eq_zero.mp hterm_zero with h0 | h0
      · linarith
      · linarith
    rw [h_eq]
    exact hval_ge τ
