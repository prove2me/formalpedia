-- Prove2me | solution 1 for TheoryOfGames.SimpleGames.three_person_is_direct_majority
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T14:56:29.612983+00:00
-- url     : https://prove2.me/submissions/602ce7a2-9948-4af0-a278-6141bb4ff1c5

import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_WinningLosing

set_option autoImplicit false

namespace P8d4f531b

lemma cases8 : ∀ S : Finset (Fin 3), S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {2} ∨
    S = {0, 1} ∨ S = {0, 2} ∨ S = {1, 2} ∨ S = Finset.univ := by decide

end P8d4f531b

open TheoryOfGames.SimpleGames in
theorem solution (v : Finset (Fin 3) → ℝ) (hv : IsCharFunction v)
    (hess : ¬ IsInessential v) :
    IsSimple v ∧ winningSets v = {S | (3 : ℝ) / 2 < (S.card : ℝ)} := by
  obtain ⟨h0, hc, hs⟩ := hv
  have h01 : v {0, 1} = -v {2} := by
    have := hc {2}; rwa [show ({2} : Finset (Fin 3))ᶜ = {0, 1} by decide] at this
  have h02 : v {0, 2} = -v {1} := by
    have := hc {1}; rwa [show ({1} : Finset (Fin 3))ᶜ = {0, 2} by decide] at this
  have h12 : v {1, 2} = -v {0} := by
    have := hc {0}; rwa [show ({0} : Finset (Fin 3))ᶜ = {1, 2} by decide] at this
  have hu : v Finset.univ = 0 := by
    have := hc ∅; rw [Finset.compl_empty, h0] at this; simpa using this
  have hsup : v {0} + v {1} ≤ v {0, 1} := by
    have := hs {0} {1} (by decide)
    rwa [show ({0} : Finset (Fin 3)) ∪ {1} = {0, 1} by decide] at this
  have hne : v {0} + v {1} + v {2} ≠ 0 := by
    intro h
    apply hess
    intro S
    rcases P8d4f531b.cases8 S with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [reducedForm, Fin.sum_univ_three, h0, h01, h02, h12, hu] <;> linarith
  have hlt : v {0} + v {1} + v {2} < 0 := lt_of_le_of_ne (by linarith) hne
  have hflat : ∀ S : Finset (Fin 3), IsFlat v S ↔ S.card ≤ 1 := by
    intro S
    rcases P8d4f531b.cases8 S with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [IsFlat, Fin.sum_univ_three, h0, h01, h02, h12, hu] <;> intro h <;> linarith
  have hwin : ∀ S : Finset (Fin 3), S ∈ winningSets v ↔ (3 : ℝ) / 2 < (S.card : ℝ) := by
    intro S
    show IsFlat v Sᶜ ↔ _
    rw [hflat, Finset.card_compl, Fintype.card_fin]
    have h3 := S.card_le_univ
    rw [Fintype.card_fin] at h3
    constructor
    · intro h
      have : 2 ≤ S.card := by omega
      have : (2 : ℝ) ≤ S.card := by exact_mod_cast this
      linarith
    · intro h
      have : (1 : ℝ) < S.card := by linarith
      have : 1 < S.card := by exact_mod_cast this
      omega
  refine ⟨⟨hess, fun S => ?_⟩, Set.ext hwin⟩
  by_cases hS : S.card ≤ 1
  · exact Or.inr ((hflat S).2 hS)
  · left
    rw [hwin]
    have : 2 ≤ S.card := by omega
    have : (2 : ℝ) ≤ S.card := by exact_mod_cast this
    linarith
