-- Prove2me | solution 1 for QueueSignal.separating_RC
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:50:53.866068+00:00
-- url     : https://prove2.me/submissions/d41e7777-db62-499f-b8d8-a62acd7ba6ac

import Mathlib
import Definitions.Def_QueueSignal_SignalingGame
import Definitions.Def_QueueSignal_QueueModel

open QueueSignal in
theorem solution (P : Params) (hP : P.Valid) (lam : ℝ) (hlam : 0 < lam) (b : Sig → ℝ) :
    IsPureSE P.δ (pay P lam) (.R, .C) b ↔
      b .R = 1 ∧ b .C = 0 ∧ lamO P lam 1 = lamU P lam 0 := by
  have hδ : 0 < P.δ := hP.2.2.2.2.1
  have hbR : bayes P.δ (.R, .C) .R = 1 := by
    unfold bayes; simp [hδ.ne']
  have hbC : bayes P.δ (.R, .C) .C = 0 := by
    unfold bayes; simp
  constructor
  · rintro ⟨_, hbay, hIC⟩
    have h1 : b .R = 1 := by rw [hbay .R (Or.inl rfl), hbR]
    have h2 : b .C = 0 := by rw [hbay .C (Or.inr rfl), hbC]
    have i1 := hIC .H .C
    have i2 := hIC .L .R
    simp only [pay, Profile.sig] at i1 i2
    rw [h1, h2] at i1 i2
    exact ⟨h1, h2, le_antisymm i2 i1⟩
  · rintro ⟨h1, h2, heq⟩
    refine ⟨?_, ?_, ?_⟩
    · intro s; cases s
      · rw [h1]; norm_num
      · rw [h2]; norm_num
    · intro s _; cases s
      · rw [h1, hbR]
      · rw [h2, hbC]
    · intro t s
      cases t <;> cases s <;> simp only [pay, Profile.sig, h1, h2, heq, le_refl]
