-- Prove2me | solution 1 for VidalHGS.Elitism.worst_biasedFitness_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-07T22:33:04.211799+00:00
-- url     : https://prove2.me/submissions/79420795-9676-4b66-af12-a55ad31dbae4

import Mathlib
import Definitions.Def_VidalHGS_Elitism_SurvivorSelection

open VidalHGS.Elitism

open Classical in
theorem solution {α : Type*} [DecidableEq α]
    (c : α → ℝ) (δ : α → α → ℝ) (Δ : Finset α → α → ℝ) (nbElit : ℕ) (best : α)
    (P : Finset α) (W : α)
    (hX : cloneSet c δ best P = ∅) (hcard : 2 ≤ P.card) (hsize : nbElit + 1 ≤ P.card)
    (hW : W ∈ P) (hworst : ∀ K ∈ P, c K ≤ c W) :
    fitRank c P W = 1 ∧ 1 ≤ biasedFitness c Δ nbElit P W := by
  have hden : (0 : ℝ) < (P.card : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hcard
    linarith
  -- X = ∅ means no non-best individual of P has a clone in P
  have hnotX : ∀ I, I ∉ cloneSet c δ best P := by
    intro I hI
    rw [hX] at hI
    simp at hI
  -- hence costs in P are pairwise distinct: every K ≠ W is strictly better than W
  have hstrict : ∀ K ∈ P, K ≠ W → c K < c W := by
    intro K hK hKW
    rcases lt_or_eq_of_le (hworst K hK) with hlt | heq
    · exact hlt
    · exfalso
      have hWclone : IsClone c δ P W := ⟨K, hK, hKW, Or.inr heq⟩
      have hKclone : IsClone c δ P K := ⟨W, hW, hKW.symm, Or.inr heq.symm⟩
      have hWbest : W = best := by
        by_contra hne
        apply hnotX W
        unfold cloneSet
        rw [Finset.mem_filter]
        exact ⟨hW, hne, hWclone⟩
      have hKbest : K = best := by
        by_contra hne
        apply hnotX K
        unfold cloneSet
        rw [Finset.mem_filter]
        exact ⟨hK, hne, hKclone⟩
      exact hKW (hKbest.trans hWbest.symm)
  -- the individuals strictly better than W are exactly P \ {W}
  have hfilter : P.filter (fun K => c K < c W) = P.erase W := by
    ext K
    rw [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hK, hlt⟩
      refine ⟨?_, hK⟩
      intro hKW
      rw [hKW] at hlt
      exact lt_irrefl _ hlt
    · rintro ⟨hKW, hK⟩
      exact ⟨hK, hstrict K hK hKW⟩
  have hfit : fitRank c P W = 1 := by
    unfold fitRank
    rw [hfilter, Finset.card_erase_of_mem hW, Nat.cast_pred (by omega)]
    exact div_self hden.ne'
  refine ⟨hfit, ?_⟩
  have hcoef : (0 : ℝ) ≤ 1 - (nbElit : ℝ) / ((P.card : ℝ) - 1) := by
    have h1 : (nbElit : ℝ) ≤ (P.card : ℝ) - 1 := by
      have : (nbElit : ℝ) + 1 ≤ (P.card : ℝ) := by exact_mod_cast hsize
      linarith
    have h2 : (nbElit : ℝ) / ((P.card : ℝ) - 1) ≤ 1 := by
      have := div_le_div_of_nonneg_right h1 hden.le
      rwa [div_self hden.ne'] at this
    linarith
  have hdc0 : 0 ≤ dcRank Δ P W := by
    unfold dcRank
    exact div_nonneg (Nat.cast_nonneg _) hden.le
  have hBF : biasedFitness c Δ nbElit P W =
      fitRank c P W + (1 - (nbElit : ℝ) / ((P.card : ℝ) - 1)) * dcRank Δ P W := rfl
  rw [hBF, hfit]
  have := mul_nonneg hcoef hdc0
  linarith
