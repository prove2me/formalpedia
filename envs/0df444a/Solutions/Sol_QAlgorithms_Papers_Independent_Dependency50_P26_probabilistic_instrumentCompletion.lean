-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P26.probabilistic_instrumentCompletion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:48:35.072965+00:00
-- url     : https://prove2.me/submissions/45474a7a-744f-42d2-af89-8e3f364c08e1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P26


/-- PDF p.16, Theorem 9: include the given probabilistic comb as an actual branch. -/
theorem solution (s : Signature) (n : ℕ)
    (R : Matrix (Basis s n) (Basis s n) ℂ) (hR : Probabilistic s n R) :
    ∃ k, ∃ P : Fin k → Matrix (Basis s n) (Basis s n) ℂ,
      CombInstrument s n k P ∧ ∃ i, P i = R := by
  obtain ⟨hn, hR0, S, hS, hSR⟩ := hR
  refine ⟨2, ![R, S - R], ⟨hn, by norm_num, ?_, ?_⟩, 0, rfl⟩
  · intro i
    fin_cases i
    · simpa using hR0
    · simpa using hSR
  · simpa [Fin.sum_univ_two] using hS


end

