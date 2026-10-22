-- Prove2me | solution 1 for TheoryOfGames.ThreePerson.lineSet_isSolution
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:03:17.3953+00:00
-- url     : https://prove2.me/submissions/da40d1bf-f490-406b-85e1-11d340133f72

import Mathlib
import Definitions.Def_TheoryOfGames_ThreePerson_Solution
import Definitions.Def_TheoryOfGames_ThreePerson_ReducedThreePerson

set_option autoImplicit false
open TheoryOfGames.ThreePerson

theorem dom_iff (α β : Fin 3 → ℝ) (hα : IsImputation redV α)
    (hβ : IsImputation redV β) :
    Dominates redV α β ↔
      (β 0 < α 0 ∧ β 1 < α 1) ∨ (β 0 < α 0 ∧ β 2 < α 2) ∨ (β 1 < α 1 ∧ β 2 < α 2) := by
  obtain ⟨hα1, hα2⟩ := hα
  obtain ⟨hβ1, hβ2⟩ := hβ
  have hv1 : ∀ i : Fin 3, redV {i} = -1 := fun i => by simp [redV]
  have hα1' : ∀ i, -1 ≤ α i := fun i => by simpa [hv1 i] using hα1 i
  have hβ1' : ∀ i, -1 ≤ β i := fun i => by simpa [hv1 i] using hβ1 i
  rw [Fin.sum_univ_three] at hα2 hβ2
  constructor
  · rintro ⟨S, hS, heff, hlt⟩
    by_cases hc : S.card = 1
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
      have h1 := heff
      simp only [IsEffective, Finset.sum_singleton, hv1] at h1
      have h2 := hlt i (Finset.mem_singleton_self i)
      have := hβ1' i
      linarith
    · have h2 : 1 < S.card := by
        have := hS.card_pos
        omega
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp h2
      have hi' := hlt i hi
      have hj' := hlt j hj
      fin_cases i <;> fin_cases j <;> simp at hij <;> simp at hi' hj' <;> tauto
  · intro h
    have e2 : ∀ i j : Fin 3, i ≠ j → redV {i, j} = 1 := by
      intro i j hij
      simp [redV, Finset.card_pair hij]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨{0, 1}, by simp, ?_, ?_⟩
      · simp only [IsEffective]
        rw [e2 0 1 (by decide)]
        simp [Finset.sum_pair (show (0 : Fin 3) ≠ 1 by decide)]
        linarith [hα1' 2]
      · intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption
    · refine ⟨{0, 2}, by simp, ?_, ?_⟩
      · simp only [IsEffective]
        rw [e2 0 2 (by decide)]
        simp [Finset.sum_pair (show (0 : Fin 3) ≠ 2 by decide)]
        linarith [hα1' 1]
      · intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption
    · refine ⟨{1, 2}, by simp, ?_, ?_⟩
      · simp only [IsEffective]
        rw [e2 1 2 (by decide)]
        simp [Finset.sum_pair (show (1 : Fin 3) ≠ 2 by decide)]
        linarith [hα1' 0]
      · intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption

theorem imp_iff (α : Fin 3 → ℝ) :
    IsImputation redV α ↔ (∀ i, -1 ≤ α i) ∧ α 0 + α 1 + α 2 = 0 := by
  have hv1 : ∀ i : Fin 3, redV {i} = -1 := fun i => by simp [redV]
  unfold IsImputation
  rw [Fin.sum_univ_three]
  simp only [hv1]


theorem core (c : ℝ) (hc1 : -1 ≤ c) (hc2 : c < 1 / 2) (x y z : ℝ) (hx : -1 ≤ x) (hy : -1 ≤ y)
    (hz : -1 ≤ z) (hs : x + y + z = 0) (hne : x ≠ c) :
    ∃ x' y' z' : ℝ, -1 ≤ y' ∧ -1 ≤ z' ∧ x' = c ∧ x' + y' + z' = 0 ∧
      ((x < x' ∧ y < y') ∨ (x < x' ∧ z < z') ∨ (y < y' ∧ z < z')) := by
  rcases lt_or_gt_of_ne hne with h | h
  · by_cases hy1 : y < 1 - c
    · refine ⟨c, (y + (1 - c)) / 2, -c - (y + (1 - c)) / 2, ?_, ?_, rfl, ?_, Or.inl ⟨h, ?_⟩⟩ <;>
        linarith
    · have hz1 : z < 1 - c := by linarith
      refine ⟨c, -c - (z + (1 - c)) / 2, (z + (1 - c)) / 2, ?_, ?_, rfl, ?_, Or.inr (Or.inl ⟨h, ?_⟩)⟩ <;>
        linarith
  · refine ⟨c, y + (x - c) / 2, z + (x - c) / 2, ?_, ?_, rfl, ?_, Or.inr (Or.inr ⟨?_, ?_⟩)⟩ <;>
      linarith

theorem solution (i : Fin 3) (c : ℝ) (hc1 : -1 ≤ c) (hc2 : c < 1 / 2) :
    IsSolution redV (lineSet i c) := by
  refine ⟨fun α hα => hα.1, ?_, ?_⟩
  · rintro α ⟨hα, hαi⟩ β ⟨hβ, hβi⟩ hdom
    rw [dom_iff α β hα hβ] at hdom
    obtain ⟨hb1, hs1⟩ := (imp_iff α).mp hα
    obtain ⟨hb2, hs2⟩ := (imp_iff β).mp hβ
    fin_cases i <;> simp at hαi hβi <;>
      rcases hdom with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> linarith
  · intro β hβ hnot
    obtain ⟨hb, hs⟩ := (imp_iff β).mp hβ
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    have hne : β i ≠ c := fun h => hnot ⟨hβ, h⟩
    fin_cases i
    · simp at hne
      obtain ⟨x', y', z', hy', hz', hx', hs', hd⟩ := core c hc1 hc2 (β 0) (β 1) (β 2) hb0 hb1 hb2 hs hne
      have hI : IsImputation redV ![x', y', z'] := by
        rw [imp_iff]
        refine ⟨fun j => ?_, by simpa using hs'⟩
        fin_cases j <;> simp <;> linarith
      refine ⟨![x', y', z'], ⟨hI, by simpa using hx'⟩, (dom_iff _ β hI hβ).mpr ?_⟩
      simpa [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] using hd
    · simp at hne
      obtain ⟨x', y', z', hy', hz', hx', hs', hd⟩ := core c hc1 hc2 (β 1) (β 0) (β 2) hb1 hb0 hb2 (by linarith) hne
      have hI : IsImputation redV ![y', x', z'] := by
        rw [imp_iff]
        refine ⟨fun j => ?_, by simp; linarith⟩
        fin_cases j <;> simp <;> linarith
      refine ⟨![y', x', z'], ⟨hI, by simpa using hx'⟩, (dom_iff _ β hI hβ).mpr ?_⟩
      simp [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
      tauto
    · simp at hne
      obtain ⟨x', y', z', hy', hz', hx', hs', hd⟩ := core c hc1 hc2 (β 2) (β 0) (β 1) hb2 hb0 hb1 (by linarith) hne
      have hI : IsImputation redV ![y', z', x'] := by
        rw [imp_iff]
        refine ⟨fun j => ?_, by simp; linarith⟩
        fin_cases j <;> simp <;> linarith
      refine ⟨![y', z', x'], ⟨hI, by simpa [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] using hx'⟩, (dom_iff _ β hI hβ).mpr ?_⟩
      simp [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
      tauto
