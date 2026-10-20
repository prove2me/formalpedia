-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P26.commonPositiveCompletion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:52:27.439477+00:00
-- url     : https://prove2.me/submissions/4b030d01-2f51-49ed-8db8-e8a4690cd627

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P26


/-- PDF p.11, Lemma 6: one positive completion serves both operators. -/
theorem solution (s : Signature) (n : ℕ)
    (R1 R2 : Matrix (Basis s (n+1)) (Basis s (n+1)) ℂ)
    (h1 : Probabilistic s (n+1) R1) (h2 : Probabilistic s (n+1) R2)
    (htrace : traceLeft R1 = traceLeft R2) :
    ∃ T, T.PosSemidef ∧ Normalized s (n+1) (R1+T) ∧
      Normalized s (n+1) (R2+T) := by
  obtain ⟨-, hR1, S, hS, hSR⟩ := h1
  obtain ⟨-, hR2, -, -, -⟩ := h2
  refine ⟨S - R1, hSR, by simpa using hS, ?_⟩
  obtain ⟨-, Q, hQ, hSt⟩ := hS
  refine ⟨hR2.add hSR, Q, hQ, ?_⟩
  rw [← hSt]
  ext a b
  have := congrFun (congrFun htrace a) b
  simp only [traceLeft, Matrix.of_apply] at this ⊢
  change ∑ x, (R2 (x, a) (x, b) + (S (x, a) (x, b) - R1 (x, a) (x, b))) = ∑ x, S (x, a) (x, b)
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  linear_combination -this


end

