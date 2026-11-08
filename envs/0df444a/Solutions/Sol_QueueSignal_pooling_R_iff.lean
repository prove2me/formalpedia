-- Prove2me | solution 1 for QueueSignal.pooling_R_iff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:05:51.283762+00:00
-- url     : https://prove2.me/submissions/447dd415-f008-4a0c-a81d-927371cc56b9

import Mathlib
import Definitions.Def_QueueSignal_SignalingGame
import Definitions.Def_QueueSignal_QueueModel

open QueueSignal in
theorem solution (P : Params) (hP : P.Valid) (lam : ℝ) (hlam : 0 < lam) :
    (∀ b : Sig → ℝ, IsPureSE P.δ (pay P lam) (.R, .R) b → b .R = P.δ) ∧
    ∀ dC : ℝ, 0 ≤ dC → dC ≤ 1 →
      (IsPureSE P.δ (pay P lam) (.R, .R) (beliefs P.δ dC) ↔ lamU P lam dC ≤ lamO P lam P.δ) := by
  have hb : bayes P.δ (Sig.R, Sig.R) Sig.R = P.δ := by simp [bayes]
  refine ⟨fun b hb' => ?_, fun dC h0 h1 => ⟨fun h => ?_, fun h => ⟨?_, ?_, ?_⟩⟩⟩
  · rw [hb'.2.1 Sig.R (Or.inl rfl), hb]
  · exact h.2.2 QType.H Sig.C
  · intro s
    cases s
    · exact ⟨hP.2.2.2.2.1.le, hP.2.2.2.2.2.le⟩
    · exact ⟨h0, h1⟩
  · intro s hs
    cases s
    · exact hb.symm
    · exfalso
      rcases hs with h' | h' <;> cases h'
  · intro t s
    cases t <;> cases s
    · exact le_refl _
    · exact h
    · exact le_refl _
    · exact h
