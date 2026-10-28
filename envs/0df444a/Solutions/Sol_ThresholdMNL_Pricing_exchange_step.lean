-- Prove2me | solution 1 for ThresholdMNL.Pricing.exchange_step
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-26T22:40:29.426039+00:00
-- url     : https://prove2.me/submissions/44d6b573-896c-4045-a9f7-fda68132da12

import Mathlib
import Definitions.Def_ThresholdMNL_Pricing_Model

open ThresholdMNL.Pricing Finset Classical

lemma exch_profit_eq {N : ℕ} (S : Finset (Fin N)) (α c : Fin N → ℝ) (β u0 Δ : ℝ)
    (p : Fin N → ℝ) :
    profit S α c β u0 Δ p =
      (∑ i ∈ S, if InCons S α β u0 Δ p i then (p i - c i) * Real.exp (nomUtil α β p i) else 0)
        / consDenom S α β u0 Δ p := by
  classical
  unfold profit consSet choiceProb
  rw [Finset.sum_filter, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

lemma exch_denom_eq {N : ℕ} (S : Finset (Fin N)) (α : Fin N → ℝ) (β u0 Δ : ℝ)
    (p : Fin N → ℝ) :
    consDenom S α β u0 Δ p =
      (if OutsideInCons S α β u0 Δ p then Real.exp u0 else 0) +
      ∑ i ∈ S, if InCons S α β u0 Δ p i then Real.exp (nomUtil α β p i) else 0 := by
  classical
  unfold consDenom consSet
  rw [Finset.sum_filter]

theorem solution {N : ℕ} (α c : Fin N → ℝ) (β u0 Δ : ℝ) (hβ : 0 < β) (hΔ : 0 ≤ Δ)
    (S : Finset (Fin N)) (p : Fin N → ℝ) (j k : Fin N) (hj : j ∈ S) (hk : k ∈ S)
    (hα : α k - β * c k < α j - β * c j)
    (hu : nomUtil α β p j < nomUtil α β p k)
    (hkin : InCons S α β u0 Δ p k) :
    let d := ((α j - β * c j) - (α k - β * c k)) / β
    let p' := Function.update (Function.update p j (c j + (p k - c k) + d)) k
                (c k + (p j - c j) - d)
    nomUtil α β p' j = nomUtil α β p k ∧ nomUtil α β p' k = nomUtil α β p j ∧
    (OutsideInCons S α β u0 Δ p' ↔ OutsideInCons S α β u0 Δ p) ∧
    ((∀ i ∈ S, InCons S α β u0 Δ p i) → ∀ i ∈ S, InCons S α β u0 Δ p' i) ∧
    consDenom S α β u0 Δ p' = consDenom S α β u0 Δ p ∧
    profit S α c β u0 Δ p < profit S α c β u0 Δ p' := by
  classical
  intro d p'
  have hjk : j ≠ k := by rintro rfl; linarith
  have hd : 0 < d := div_pos (by linarith) hβ
  have hβd : β * d = (α j - β * c j) - (α k - β * c k) := by
    simp only [d]; field_simp
  set σ : Equiv.Perm (Fin N) := Equiv.swap j k with hσ
  have hp'j : p' j = c j + (p k - c k) + d := by
    simp [p', hjk]
  have hp'k : p' k = c k + (p j - c j) - d := by
    simp [p']
  have hp'o : ∀ i, i ≠ j → i ≠ k → p' i = p i := by
    intro i h1 h2; simp [p', h1, h2]
  have hu' : ∀ i, nomUtil α β p' i = nomUtil α β p (σ i) := by
    intro i
    by_cases h1 : i = j
    · subst h1; rw [hσ, Equiv.swap_apply_left]; simp only [nomUtil]; rw [hp'j]
      linear_combination (-1 : ℝ) * hβd
    by_cases h2 : i = k
    · subst h2; rw [hσ, Equiv.swap_apply_right]; simp only [nomUtil]; rw [hp'k]
      linear_combination hβd
    rw [hσ, Equiv.swap_apply_of_ne_of_ne h1 h2]; simp only [nomUtil]; rw [hp'o i h1 h2]
  have hσS : ∀ i, σ i ∈ S ↔ i ∈ S := by
    intro i
    by_cases h1 : i = j
    · subst h1; rw [hσ, Equiv.swap_apply_left]; simp [hj, hk]
    by_cases h2 : i = k
    · subst h2; rw [hσ, Equiv.swap_apply_right]; simp [hj, hk]
    rw [hσ, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hall : ∀ x, (∀ l ∈ S, nomUtil α β p' l - Δ ≤ x) ↔ (∀ l ∈ S, nomUtil α β p l - Δ ≤ x) := by
    intro x
    constructor
    · intro h l hl
      have := h (σ l) ((hσS l).2 hl)
      rw [hu', hσ, Equiv.swap_apply_self] at this
      exact this
    · intro h l hl
      rw [hu']
      exact h (σ l) ((hσS l).2 hl)
  have hOut : OutsideInCons S α β u0 Δ p' ↔ OutsideInCons S α β u0 Δ p := hall u0
  have hIn : ∀ i, InCons S α β u0 Δ p' i ↔ InCons S α β u0 Δ p (σ i) := by
    intro i
    unfold InCons
    rw [hu', hall, hσS]
  have hsupp : {a | σ a ≠ a} ⊆ (S : Set (Fin N)) := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha
    by_cases h1 : a = j
    · subst h1; exact hj
    by_cases h2 : a = k
    · subst h2; exact hk
    exact absurd (by rw [hσ, Equiv.swap_apply_of_ne_of_ne h1 h2]) ha
  have hDen : consDenom S α β u0 Δ p' = consDenom S α β u0 Δ p := by
    rw [exch_denom_eq, exch_denom_eq]
    congr 1
    · simp only [hOut]
    · have : ∀ i, (if InCons S α β u0 Δ p' i then Real.exp (nomUtil α β p' i) else 0) =
          (fun x => if InCons S α β u0 Δ p x then Real.exp (nomUtil α β p x) else 0) (σ i) := by
        intro i; simp only [hIn, hu']
      simp only [this]
      exact Equiv.Perm.sum_comp σ S (fun x => if InCons S α β u0 Δ p x then Real.exp (nomUtil α β p x) else 0) hsupp
  have hDpos : 0 < consDenom S α β u0 Δ p := by
    rw [exch_denom_eq]
    have h1 : 0 ≤ (if OutsideInCons S α β u0 Δ p then Real.exp u0 else 0) := by
      split_ifs <;> positivity
    have h2 : Real.exp (nomUtil α β p k) ≤
        ∑ i ∈ S, if InCons S α β u0 Δ p i then Real.exp (nomUtil α β p i) else 0 := by
      have := Finset.single_le_sum (f := fun i =>
          if InCons S α β u0 Δ p i then Real.exp (nomUtil α β p i) else 0)
        (fun i _ => by split_ifs <;> positivity) hk
      simpa [hkin] using this
    have h3 := Real.exp_pos (nomUtil α β p k)
    linarith
  refine ⟨?_, ?_, hOut, ?_, hDen, ?_⟩
  · rw [hu', hσ, Equiv.swap_apply_left]
  · rw [hu', hσ, Equiv.swap_apply_right]
  · intro h i hi
    exact (hIn i).2 (h (σ i) ((hσS i).2 hi))
  · rw [exch_profit_eq, exch_profit_eq, hDen]
    apply div_lt_div_of_pos_right _ hDpos
    set F : Fin N → ℝ := fun x =>
      if InCons S α β u0 Δ p x then (p x - c x) * Real.exp (nomUtil α β p x) else 0 with hF
    have hN0 : ∑ i ∈ S, F (σ i) = ∑ i ∈ S, F i := Equiv.Perm.sum_comp σ S F hsupp
    set G : Fin N → ℝ := fun i =>
      if InCons S α β u0 Δ p' i then (p' i - c i) * Real.exp (nomUtil α β p' i) else 0 with hG
    have hdiff : ∑ i ∈ S, (G i - F (σ i)) = (G j - F (σ j)) + (G k - F (σ k)) := by
      apply Finset.sum_eq_add_of_mem j k hj hk hjk
      intro i _ hi
      simp only [hG, hF, hIn, hu', hp'o i hi.1 hi.2, hσ, Equiv.swap_apply_of_ne_of_ne hi.1 hi.2]
      ring
    have hGj : G j - F (σ j) = d * Real.exp (nomUtil α β p k) := by
      simp only [hG, hF, hIn, hu', hσ, Equiv.swap_apply_left, hkin, if_true, hp'j]
      ring
    have hGk : G k - F (σ k) ≥ - (d * Real.exp (nomUtil α β p j)) := by
      simp only [hG, hF, hIn, hu', hσ, Equiv.swap_apply_right, hp'k]
      split_ifs
      · linarith
      · have : 0 ≤ d * Real.exp (nomUtil α β p j) := by positivity
        linarith
    have hexp : Real.exp (nomUtil α β p j) < Real.exp (nomUtil α β p k) := Real.exp_lt_exp.2 hu
    have hpos : 0 < d * Real.exp (nomUtil α β p k) - d * Real.exp (nomUtil α β p j) := by
      rw [← mul_sub]; exact mul_pos hd (by linarith)
    have hsum : ∑ i ∈ S, G i - ∑ i ∈ S, F i > 0 := by
      rw [← hN0, ← Finset.sum_sub_distrib, hdiff, hGj]; linarith
    show ∑ i ∈ S, F i < ∑ i ∈ S, G i
    linarith
