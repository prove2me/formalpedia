-- Prove2me | solution 1 for QuantumParallelRepetition.spectralSupportProjection_mul_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/fb97cfb9-e05a-4f36-b9b3-801ea5210dcb

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_spectralSupportProjection_isHermitian
import Theorems.Thm_QuantumParallelRepetition_posSemidef_mul_spectralSupportProjection

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    {d : Type*} [Fintype d] [DecidableEq d]
    {F A : Matrix d d ℂ}
    (hF : F.PosSemidef) (hA : A.PosSemidef)
    (hsub : (F - A).PosSemidef) :
    spectralSupportProjection F hF * A = A := by
  have h := congrArg Matrix.conjTranspose
    (posSemidef_mul_spectralSupportProjection hF hA hsub)
  simpa [Matrix.conjTranspose_mul,
    (spectralSupportProjection_isHermitian F hF).eq,
    hA.isHermitian.eq] using h
end QuantumParallelRepetition
