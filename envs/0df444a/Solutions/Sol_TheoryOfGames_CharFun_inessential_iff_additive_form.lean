-- Prove2me | solution 1 for TheoryOfGames.CharFun.inessential_iff_additive_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T11:52:44.688748+00:00
-- url     : https://prove2.me/submissions/24755870-29a3-464e-a470-e2d47710d596

import Mathlib
import Definitions.Def_TheoryOfGames_CharFun_IsCharFunction
import Definitions.Def_TheoryOfGames_CharFun_StrategicEquivalence

open TheoryOfGames.CharFun in
theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : IsCharFunction v) :
    IsInessential v ↔ ∃ α : Fin n → ℝ, ∀ S : Finset (Fin n), v S = ∑ k ∈ S, α k := by
  constructor
  · intro h
    refine ⟨fun k => v {k} - (1 / (n : ℝ)) * ∑ j : Fin n, v {j}, fun S => ?_⟩
    have hS := h S
    unfold reducedForm at hS
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib] at hS
    rw [Finset.sum_sub_distrib]
    linarith
  · rintro ⟨α, hα⟩ S
    have hk : ∀ k, v {k} = α k := fun k => by rw [hα]; simp
    have huniv : ∑ j : Fin n, α j = 0 := by
      have h1 : v Finset.univ = 0 := by
        have := hv.2.1 ∅
        rw [Finset.compl_empty, hv.1] at this
        simpa using this
      rw [hα] at h1
      exact h1
    unfold reducedForm
    simp only [hk, huniv, mul_zero, add_zero, Finset.sum_neg_distrib, ← hα]
    ring
