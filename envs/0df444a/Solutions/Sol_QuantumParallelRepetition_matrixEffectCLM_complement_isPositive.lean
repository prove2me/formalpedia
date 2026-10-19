-- Prove2me | solution 1 for QuantumParallelRepetition.matrixEffectCLM_complement_isPositive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/229ab6c6-e6a5-4fb4-a075-9f86ec2ef687

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_matrixEffectCLM_isPositive

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace QuantumParallelRepetition
theorem _root_.solution
    {d : Type*} [Fintype d] [DecidableEq d]
    (E : Matrix d d ℂ) (hE : (1 - E).PosSemidef) :
    (1 - Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) E).IsPositive := by
  simpa using matrixEffectCLM_isPositive (1 - E) hE
end QuantumParallelRepetition
