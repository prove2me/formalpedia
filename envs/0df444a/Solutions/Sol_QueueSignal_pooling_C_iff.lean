-- Prove2me | solution 1 for QueueSignal.pooling_C_iff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:08:56.135653+00:00
-- url     : https://prove2.me/submissions/fa4549ed-9076-4aaf-9bf6-c13834636bee

import Mathlib
import Definitions.Def_QueueSignal_SignalingGame
import Definitions.Def_QueueSignal_QueueModel

open QueueSignal in
theorem solution (P : Params) (hP : P.Valid) (lam : ℝ) (hlam : 0 < lam) :
    (∀ b : Sig → ℝ, IsPureSE P.δ (pay P lam) (.C, .C) b → b .C = P.δ) ∧
    ∀ dR : ℝ, 0 ≤ dR → dR ≤ 1 →
      (IsPureSE P.δ (pay P lam) (.C, .C) (beliefs dR P.δ) ↔ lamO P lam dR ≤ lamU P lam P.δ) := by
  have hb : bayes P.δ (Sig.C, Sig.C) Sig.C = P.δ := by simp [bayes]
  refine ⟨fun b hb' => ?_, fun dR h0 h1 => ⟨fun h => ?_, fun h => ⟨?_, ?_, ?_⟩⟩⟩
  · rw [hb'.2.1 Sig.C (Or.inl rfl), hb]
  · exact h.2.2 QType.H Sig.R
  · intro s
    cases s
    · exact ⟨h0, h1⟩
    · exact ⟨hP.2.2.2.2.1.le, hP.2.2.2.2.2.le⟩
  · intro s hs
    cases s
    · exfalso
      rcases hs with h' | h' <;> cases h'
    · exact hb.symm
  · intro t s
    cases t <;> cases s
    · exact h
    · exact le_refl _
    · exact h
    · exact le_refl _
