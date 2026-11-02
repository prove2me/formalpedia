-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P96.ring_phase_hadamard_adjoint_watrous
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:17:15.956777+00:00
-- url     : https://prove2.me/submissions/9ac8c663-8377-4233-99b3-d4c8c4c3fa47

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P96

noncomputable section

open scoped BigOperators
open QAlgorithms.Papers.Independent.Intakethird100.P96

theorem solution (extra : ℕ) :
    IsWatrous extra (star (ringPhase extra * ringHadamard extra)) := by
  refine ⟨fun bit input =>
    ((if bit = true ∧ input 0 = true then (-1 : ℂ) else 1) / (Real.sqrt 2 : ℂ)) *
      (if input 0 = true ∧ input 1 = true then (-1 : ℂ) else 1), ?_⟩
  intro a b
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, ringPhase,
    Matrix.diagonal_mul, ringHadamard, Finset.prod_mul_distrib]
  simp [star_mul, star_prod, apply_ite, and_comm, mul_comm]

end
