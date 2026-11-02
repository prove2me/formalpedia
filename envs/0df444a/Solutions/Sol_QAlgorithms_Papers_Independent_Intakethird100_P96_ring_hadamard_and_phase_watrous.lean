-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P96.ring_hadamard_and_phase_watrous
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:12:22.203882+00:00
-- url     : https://prove2.me/submissions/ebbc8a37-ff9b-4496-b2b8-840ef03e87b4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P96

noncomputable section

open scoped BigOperators
open QAlgorithms.Papers.Independent.Intakethird100.P96

namespace QCAIndividual

theorem hadamard_isWatrous (extra : ℕ) :
    IsWatrous extra (ringHadamard extra) := by
  refine ⟨fun bit input =>
    (if bit = true ∧ input 0 = true then (-1 : ℂ) else 1) / (Real.sqrt 2 : ℂ), ?_⟩
  intro a b
  simp [ringHadamard]

theorem phase_isWatrous (extra : ℕ) :
    IsWatrous extra (ringPhase extra) := by
  refine ⟨fun bit input =>
    if bit = input 0 then
      if input 0 = true ∧ input 1 = true then (-1 : ℂ) else 1
    else 0, ?_⟩
  intro a b
  by_cases h : a = b
  · subst a
    simp [ringPhase]
  · simp only [ringPhase, Matrix.diagonal_apply, if_neg h]
    symm
    obtain ⟨x, hx⟩ : ∃ x, a x ≠ b x :=
      not_forall.mp (fun hall => h (funext hall))
    exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [hx])

end QCAIndividual

open QAlgorithms.Papers.Independent.Intakethird100.P96

theorem solution (extra : ℕ) :
    IsWatrous extra (ringHadamard extra) ∧ IsWatrous extra (ringPhase extra) :=
  ⟨QCAIndividual.hadamard_isWatrous extra, QCAIndividual.phase_isWatrous extra⟩
