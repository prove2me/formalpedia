-- Prove2me | solution 1 for QuantumParallelRepetition.mul_spectralSupportProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/92987870-83df-475a-94d3-8a7cd7e06569

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_spectralSupportProjection_isHermitian
import Theorems.Thm_QuantumParallelRepetition_spectralSupportProjection_mul

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    F * spectralSupportProjection F hF = F := by
  have h := congrArg Matrix.conjTranspose
    (spectralSupportProjection_mul F hF)
  simpa [Matrix.conjTranspose_mul,
    (spectralSupportProjection_isHermitian F hF).eq,
    hF.isHermitian.eq] using h
end QuantumParallelRepetition
