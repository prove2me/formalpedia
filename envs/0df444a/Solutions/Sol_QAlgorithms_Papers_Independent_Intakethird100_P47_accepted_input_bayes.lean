-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P47.accepted_input_bayes
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T18:42:17.141428+00:00
-- url     : https://prove2.me/submissions/d5a1047b-f57c-49c2-a010-afc31b15636c

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P47

open scoped ComplexConjugate

open scoped BigOperators

open QAlgorithms.Papers.Independent.Intakethird100.P47 in
theorem solution (p : Behavior) (w : PairLaw)
    (hp : IsBehavior p) (hw : IsPairLaw w) (hs : 0 < siftingProbability p w) :
    siftingProbability p w = aliceMass p w false + aliceMass p w true ∧
    aliceMass p w false =
      p false false false false * w false false + p false true false false * w false true ∧
    aliceMass p w true =
      p true false false false * w true false + p true true false false * w true true ∧
    aliceMarginal (acceptedLaw p w) false =
      aliceMass p w false / (aliceMass p w false + aliceMass p w true) ∧
    aliceMarginal (acceptedLaw p w) true =
      aliceMass p w true / (aliceMass p w false + aliceMass p w true) := by
  have hS : siftingProbability p w = aliceMass p w false + aliceMass p w true := by
    simp only [siftingProbability, aliceMass, Fintype.sum_bool]
    ring
  refine ⟨hS, ?_, ?_, ?_, ?_⟩
  · simp only [aliceMass, acceptedMass, Fintype.sum_bool]
    ring
  · simp only [aliceMass, acceptedMass, Fintype.sum_bool]
    ring
  · rw [← hS]
    simp only [aliceMarginal, acceptedLaw, aliceMass, Finset.sum_div]
  · rw [← hS]
    simp only [aliceMarginal, acceptedLaw, aliceMass, Finset.sum_div]
