-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P43.coefficient_rank_identification
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:38:12.287882+00:00
-- url     : https://prove2.me/submissions/d86f1502-1c1b-43a9-8570-e3eacf8709d5

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P43

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P50 (Bipartite schmidtNumber)
open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Intake100.P43 in
theorem solution (dA dB r : ℕ)
    (hA : 0 < dA) (hAB : dA ≤ dB) (hr : 1 ≤ r) (hrA : r ≤ dA) :
    (∀ v : Bipartite dA dB, Matrix.rank (coefficientEquiv v) = schmidtNumber v) ∧
    Set.BijOn (coefficientEquiv (dA := dA) (dB := dB))
      {v | v ≠ 0 ∧ schmidtNumber v = r}
      {M | Matrix.rank M = r} := by
  have h1 : ∀ v : Bipartite dA dB, Matrix.rank (coefficientEquiv v) = schmidtNumber v :=
    fun v => rfl
  refine ⟨h1, ?_, ?_, ?_⟩
  · intro v hv
    simp only [Set.mem_setOf_eq] at hv ⊢
    rw [h1]
    exact hv.2
  · intro v _ w _ h
    exact (coefficientEquiv (dA := dA) (dB := dB)).injective h
  · intro M hM
    simp only [Set.mem_setOf_eq] at hM
    refine ⟨(coefficientEquiv (dA := dA) (dB := dB)).symm M, ⟨?_, ?_⟩, by simp⟩
    · intro h0
      have hM0 : M = 0 := by
        have := congrArg (coefficientEquiv (dA := dA) (dB := dB)) h0
        simpa using this
      rw [hM0, Matrix.rank_zero] at hM
      omega
    · rw [← h1]
      simpa using hM
