-- Prove2me | solution 1 for ShortTermism.Commitment.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T03:57:00.921636+00:00
-- url     : https://prove2.me/submissions/467873c3-036d-4f2d-9e35-e9d326f48a34

import Mathlib
import Definitions.Def_ShortTermism_Commitment_Model
import Theorems.Thm_ShortTermism_Commitment_eq_A_26

open ShortTermism.Commitment

theorem solution (P : Params) (hP : P.Standing) (C : ℝ)
    (fu au eu : ℝ → ℝ) (hv : IsUnleveredValue P fu) (hu : IsUnleveredPolicy P fu au eu)
    (f : ℝ → ℝ) (dB : ℝ) :
    SolvesNU P C au f dB ↔ SolvesNO P C au eu f dB := by
  constructor
  · rintro ⟨hB, hNU⟩
    refine ⟨hB, fun δ hδ => ?_⟩
    have hδ' : P.dlow ≤ δ := le_trans hB.1 hδ.le
    exact (hNU δ hδ).unique (eq_A_26 P hP fu au eu hv hu C f δ hδ')
  · rintro ⟨hB, hNO⟩
    refine ⟨hB, fun δ hδ => ?_⟩
    have hδ' : P.dlow ≤ δ := le_trans hB.1 hδ.le
    rw [hNO δ hδ]
    exact eq_A_26 P hP fu au eu hv hu C f δ hδ'
