-- Prove2me | solution 1 for QueueSignal.separating_CR
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:29:31.615739+00:00
-- url     : https://prove2.me/submissions/8b9e7b05-b0d7-47bf-8493-9513698d4eb7

import Mathlib
import Definitions.Def_QueueSignal_SignalingGame
import Definitions.Def_QueueSignal_QueueModel

open QueueSignal in
theorem solution (P : QueueSignal.Params) (hP : P.Valid) (lam : ℝ) (hlam : 0 < lam) (b : QueueSignal.Sig → ℝ) :
    QueueSignal.IsPureSE P.δ (QueueSignal.pay P lam) (.C, .R) b ↔
      b .R = 0 ∧ b .C = 1 ∧ QueueSignal.lamO P lam 0 = QueueSignal.lamU P lam 1 := by
  have hδ0 : 0 < P.δ := hP.2.2.2.2.1
  have hbC : QueueSignal.bayes P.δ (.C, .R) .C = 1 := by
    unfold QueueSignal.bayes
    simp [hδ0.ne']
  have hbR : QueueSignal.bayes P.δ (.C, .R) .R = 0 := by
    unfold QueueSignal.bayes
    simp
  constructor
  · rintro ⟨hb, hon, hic⟩
    have e1 : b .R = 0 := by rw [hon .R (Or.inr rfl), hbR]
    have e2 : b .C = 1 := by rw [hon .C (Or.inl rfl), hbC]
    have i1 := hic .H .R
    have i2 := hic .L .C
    simp only [QueueSignal.Profile.sig, QueueSignal.pay, e1, e2] at i1 i2
    exact ⟨e1, e2, le_antisymm i1 i2⟩
  · rintro ⟨e1, e2, e3⟩
    refine ⟨fun s => ?_, fun s _ => ?_, fun t s => ?_⟩
    · cases s <;> simp [e1, e2]
    · cases s
      · rw [e1, hbR]
      · rw [e2, hbC]
    · cases t <;> cases s <;> simp only [QueueSignal.Profile.sig, QueueSignal.pay, e1, e2, e3, le_refl]
