-- Prove2me | solution 1 for QuantumSDP18.MeasureBE.trace_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:09:32.314125+00:00
-- url     : https://prove2.me/submissions/9bfb707c-e81c-493e-ab17-291eac249e0b

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QuantumSDP18_MeasureBE_Setting

set_option autoImplicit false
open QuantumSDP18.MeasureBE

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℕ)
    (U : Matrix (ι × Anc c) (ι × Anc c) ℂ) (ρ : Matrix ι ι ℂ) :
    embedZero c ρ = ketZero (ι := ι) c * ρ * (ketZero (ι := ι) c).conjTranspose ∧
      accProb c U ρ = (blockK c U * ρ).trace := by
  have h1 : embedZero c ρ = ketZero (ι := ι) c * ρ * (ketZero (ι := ι) c).conjTranspose := by
    ext ⟨i, z⟩ ⟨j, w⟩
    simp only [embedZero, zeroProj, ketZero, Matrix.kroneckerMap_apply, Matrix.of_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply]
    by_cases hz : z = ancZero c <;> by_cases hw : w = ancZero c <;> simp [hz, hw]
  refine ⟨h1, ?_⟩
  unfold accProb blockK
  rw [h1]
  have h2 : accProj (ι := ι) c * U * (ketZero (ι := ι) c * ρ * (ketZero (ι := ι) c).conjTranspose) *
      U.conjTranspose = (accProj (ι := ι) c * U * ketZero (ι := ι) c * ρ) *
        ((ketZero (ι := ι) c).conjTranspose * U.conjTranspose) := by
    simp only [Matrix.mul_assoc]
  rw [h2, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
