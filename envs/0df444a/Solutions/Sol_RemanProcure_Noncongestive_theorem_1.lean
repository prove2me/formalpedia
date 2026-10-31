-- Prove2me | solution 1 for RemanProcure.Noncongestive.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:17:18.238989+00:00
-- url     : https://prove2.me/submissions/e325ec4c-336b-453c-97a4-837b6022c1e3

import Mathlib
import Definitions.Def_RemanProcure_Noncongestive_Model
import Theorems.Thm_RemanProcure_Noncongestive_lemma_1_vstar
import Theorems.Thm_RemanProcure_Noncongestive_claim_A5_l1
import Theorems.Thm_RemanProcure_Noncongestive_claim_A6_l1

open RemanProcure.Noncongestive

theorem solution {K : ℕ} (P : Params K) (hP : Standing P) : (∀ x : Fin K → ℕ, AcqOpt P x ↔ ∀ i, ((x i : ℕ) : ℕ∞) < Sstar P i x) ∧ (∀ (i j : Fin K), j ≠ i → ∀ x : Fin K → ℕ, Sstar P i (x + e j) ≤ Sstar P i x) ∧ (∀ (i q w : Fin K), q < w → q ≠ i → w ≠ i → ∀ x : Fin K → ℕ, Sstar P i (x + e q) ≤ Sstar P i (x + e w)) ∧ (∀ x : Fin K → ℕ, (∃ i, 0 < x i) → ∃ i, 0 < x i ∧ vstar P (x - e i) + P.r i ≤ vstar P x + P.cL) ∧ (∀ (x : Fin K → ℕ) (i : Fin K), 0 < x i → (∀ j, j < i → x j = 0) → ∀ j, 0 < x j → vstar P (x - e i) + P.r i ≤ vstar P (x - e j) + P.r j) := by
  have hV := lemma_1_vstar P hP
  obtain ⟨hA1, hA2, -, -, -, -⟩ := hV
  have hA5 := claim_A5_l1 P hP
  have hA6 := claim_A6_l1 P hP
  have hK : 0 < K := hP.1
  -- update + unit vector identities
  have upd_e : ∀ (x : Fin K → ℕ) (i j : Fin K), j ≠ i → ∀ n : ℕ,
      Function.update (x + e j) i n = Function.update x i n + e j := by
    intro x i j hji n
    funext k
    by_cases hk : k = i
    · subst hk
      simp [e, Function.update_apply, Pi.single_apply, Ne.symm hji]
    · simp [e, Function.update_apply, Pi.single_apply, hk]
  have upd_succ : ∀ (x : Fin K → ℕ) (i : Fin K) (n : ℕ),
      Function.update x i (n + 1) = Function.update x i n + e i := by
    intro x i n
    funext k
    by_cases hk : k = i
    · subst hk; simp [e]
    · simp [e, Function.update_apply, Pi.single_apply, hk]
  have upd_mono : ∀ (x : Fin K → ℕ) (i : Fin K) (n k : ℕ),
      acqGap P (Function.update x i n) ≤ acqGap P (Function.update x i (n + k)) := by
    intro x i n k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← add_assoc, upd_succ]
      exact ih.trans (hA5 _ _)
  have sub_add : ∀ (x : Fin K → ℕ) (i : Fin K), 0 < x i → x - e i + e i = x := by
    intro x i hi
    funext k
    by_cases hk : k = i
    · subst hk; simp [e]; omega
    · simp [e, Pi.single_apply, hk]
  -- characterization of `x i < Sstar`
  have lt_S : ∀ (x : Fin K → ℕ) (i : Fin K),
      ((x i : ℕ) : ℕ∞) < Sstar P i x ↔
        ∀ n : ℕ, ¬ AcqOpt P (Function.update x i n) → x i < n := by
    intro x i
    rw [← Order.add_one_le_iff_of_not_isMax (by simp)]
    unfold Sstar
    simp only [le_iInf_iff]
    constructor
    · intro h n hn
      have := h n hn
      have h2 : ((x i + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast this
      exact_mod_cast h2
    · intro h n hn
      have := h n hn
      have h2 : ((x i + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast this
      exact_mod_cast h2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx i
      rw [lt_S]
      intro n hn
      by_contra hlt
      push_neg at hlt
      apply hn
      have := upd_mono x i n (x i - n)
      rw [Nat.add_sub_cancel' hlt, Function.update_eq_self] at this
      exact this.trans hx
    · intro h
      have := (lt_S x ⟨0, hK⟩).1 (h ⟨0, hK⟩) (x ⟨0, hK⟩)
      by_contra hc
      rw [Function.update_eq_self] at this
      exact lt_irrefl _ (this hc)
  · intro i j hji x
    unfold Sstar
    refine le_iInf₂ fun n hn => iInf₂_le n ?_
    intro hacq
    apply hn
    unfold AcqOpt at *
    rw [upd_e x i j hji n] at hacq
    exact (hA5 _ j).trans hacq
  · intro i q w hqw hqi hwi x
    unfold Sstar
    refine le_iInf₂ fun n hn => iInf₂_le n ?_
    intro hacq
    apply hn
    unfold AcqOpt at *
    rw [upd_e x i q hqi n] at hacq
    rw [upd_e x i w hwi n]
    exact (hA6 _ q w hqw).trans hacq
  · rintro x ⟨i, hi⟩
    refine ⟨i, hi, ?_⟩
    have := hA1 (x - e i) i
    rw [sub_add x i hi] at this
    linarith
  · intro x i hi hbest j hj
    by_cases hji : j = i
    · subst hji; exact le_rfl
    have hij : i < j := by
      rcases lt_or_gt_of_ne hji with h | h
      · exact absurd (hbest j h) (by omega)
      · exact h
    have := hA2 (x - e i - e j) i j hij
    have hxj : 0 < (x - e i) j := by
      simp [e, Pi.single_apply, hji]; exact hj
    have hxi : 0 < (x - e j) i := by
      simp [e, Pi.single_apply, Ne.symm hji]; exact hi
    have h1 : x - e i - e j + e i = x - e j := by
      rw [show x - e i - e j = x - e j - e i by
        funext k; simp only [Pi.sub_apply]; omega]
      exact sub_add _ i hxi
    rw [h1, sub_add _ j hxj] at this
    linarith
