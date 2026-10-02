-- Prove2me | solution 1 for TheoryOfGames.GeneralGames.negation_iff_constantSum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T10:17:02.647333+00:00
-- url     : https://prove2.me/submissions/346ec7e6-ddcb-4ef7-b10f-2f40f0671608

import Mathlib
import Definitions.Def_TheoryOfGames_GeneralGames_CharFunConditions

set_option autoImplicit false

open TheoryOfGames.GeneralGames in
theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : IsRestrictedCharFunction v) :
    (∀ S : Finset (Fin n), v Sᶜ = -v S) ↔
      ((∀ S : Finset (Fin n), v S + v Sᶜ = v Finset.univ) ∧ v Finset.univ = 0) := by
  have h0 : v ∅ = 0 := hv.1
  constructor
  · intro h
    have hu : v Finset.univ = 0 := by
      have := h ∅
      rw [Finset.compl_empty] at this
      rw [this, h0, neg_zero]
    refine ⟨fun S => ?_, hu⟩
    rw [h S, hu]
    ring
  · rintro ⟨h1, h2⟩ S
    have := h1 S
    rw [h2] at this
    linarith
