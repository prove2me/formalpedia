-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P26.external_operationalEquivalence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:48:24.113312+00:00
-- url     : https://prove2.me/submissions/2f66df0f-16a9-416f-825a-d97915336c36

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P26


/-- PDF p.9, Eq.(38): generalized Born rule and forward operational equivalence for
external experiments on deterministic or probabilistic networks. Their Choi operators
are probabilistic combs (Definition 4); deterministic combs are included by taking
themselves as their deterministic upper bound. Only external input/output experiments
are compared, as specified in the source. -/
theorem solution (s : Signature) (n k : ℕ)
    (P : Fin k → Matrix (Basis s n) (Basis s n) ℂ) (hP : CombTester s n k P)
    (R S : Matrix (Basis s n) (Basis s n) ℂ)
    (hR : Probabilistic s n R) (hS : Probabilistic s n S) (h : R = S) :
    (∀ i, externalProbability s n R (P i) = QAlgorithms.effectProb (P i).transpose R) ∧
      (∀ i, externalProbability s n R (P i) = externalProbability s n S (P i)) := by
  subst h
  refine ⟨fun i => ?_, fun i => rfl⟩
  simp only [externalProbability, QAlgorithms.effectProb, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring


end

