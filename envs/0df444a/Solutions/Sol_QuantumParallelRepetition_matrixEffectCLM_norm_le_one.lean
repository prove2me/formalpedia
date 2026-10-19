-- Prove2me | solution 1 for QuantumParallelRepetition.matrixEffectCLM_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/8a07e0c2-b439-4ee3-9203-e5f0e21444fc

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_matrixEffectCLM_isPositive
import Theorems.Thm_QuantumParallelRepetition_matrixEffectCLM_complement_isPositive

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace QuantumParallelRepetition
theorem _root_.solution
    {d : Type*} [Fintype d] [DecidableEq d]
    (E : Matrix d d ℂ) (hE : E.PosSemidef)
    (h_complement : (1 - E).PosSemidef) :
    ‖Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) E‖ ≤ 1 := by
  have h_positive := matrixEffectCLM_isPositive E hE
  have h_nonneg :
      0 ≤ Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) E :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr h_positive
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ h_nonneg).mpr
  exact (ContinuousLinearMap.le_def _ _).mpr
    (matrixEffectCLM_complement_isPositive E h_complement)
end QuantumParallelRepetition
