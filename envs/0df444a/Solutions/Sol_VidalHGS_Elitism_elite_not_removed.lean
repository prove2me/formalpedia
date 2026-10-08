-- Prove2me | solution 1 for VidalHGS.Elitism.elite_not_removed
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-07T22:36:13.245997+00:00
-- url     : https://prove2.me/submissions/1fe0e4df-f3f1-4f2d-9fad-91035b900358

import Mathlib
import Definitions.Def_VidalHGS_Elitism_SurvivorSelection
import Theorems.Thm_VidalHGS_Elitism_removalStep_keeps_elite

open VidalHGS.Elitism

open Classical in
theorem solution {α : Type*} [DecidableEq α]
    (c : α → ℝ) (δ : α → α → ℝ) (Δ : Finset α → α → ℝ) (nbElit : ℕ) (best : α)
    (nOff : ℕ) (P P' : Finset α) (J : α)
    (hrun : SurvivorRun c δ Δ nbElit best nOff P P') (hsize : nbElit + nOff ≤ P.card)
    (hJ : J ∈ P) (hJX : J ∉ cloneSet c δ best P) (helite : IsElite c nbElit P J) :
    J ∈ P' := by
  -- "J ∉ X" is preserved when the population shrinks: a clone in Q ⊆ P is a clone in P
  have hX_mono : ∀ {P Q : Finset α}, Q ⊆ P →
      J ∉ cloneSet c δ best P → J ∉ cloneSet c δ best Q := by
    intro P Q hQP hJP hJQ
    apply hJP
    unfold cloneSet at hJQ ⊢
    rw [Finset.mem_filter] at hJQ ⊢
    obtain ⟨hJQ', hne, hclone⟩ := hJQ
    obtain ⟨K, hKQ, hKJ, hor⟩ := hclone
    exact ⟨hQP hJQ', hne, K, hQP hKQ, hKJ, hor⟩
  -- being among the nbElit best is preserved when the population shrinks
  have helite_mono : ∀ {P Q : Finset α}, Q ⊆ P →
      IsElite c nbElit P J → IsElite c nbElit Q J := by
    intro P Q hQP h
    unfold IsElite at h ⊢
    exact lt_of_le_of_lt (Finset.card_le_card (Finset.filter_subset_filter _ hQP)) h
  -- induction on the run: each removal step spares J and keeps the size condition
  have key : ∀ (n : ℕ) (P R : Finset α), SurvivorRun c δ Δ nbElit best n P R →
      nbElit + n ≤ P.card → J ∈ P → J ∉ cloneSet c δ best P → IsElite c nbElit P J →
        J ∈ R := by
    intro n P R h
    induction h with
    | zero P =>
      intro _ hJ _ _
      exact hJ
    | @succ n P Q R hstep hrest ih =>
      intro hsize hJ hJX helite
      have hJQ : J ∈ Q :=
        removalStep_keeps_elite c δ Δ nbElit best P Q J hstep (by omega) hJ hJX helite
      obtain ⟨I, hI, hQ, -, -⟩ := hstep
      have hQP : Q ⊆ P := by
        rw [hQ]
        exact Finset.erase_subset I P
      have hcardQ : Q.card = P.card - 1 := by
        rw [hQ]
        exact Finset.card_erase_of_mem hI
      exact ih (by omega) hJQ (hX_mono hQP hJX) (helite_mono hQP helite)
  exact key nOff P P' hrun hsize hJ hJX helite
