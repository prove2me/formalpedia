-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourcePhaseHarmonicWork_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/f1107cef-9293-4243-95f8-cda4a35f0644

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalMatchedVerifierTensor_norm

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
namespace QuantumParallelRepetition
theorem _root_.solution
    {P k : ℕ} (phases : 0 < P) (harmonic : 0 < k) :
    ‖unconditionalActualFairSourcePhaseHarmonicWork P k‖ = 1 := by
  unfold unconditionalActualFairSourcePhaseHarmonicWork
  rw [LinearIsometryEquiv.norm_map,
    unconditionalMatchedVerifierTensor_norm,
    ePRState_norm P phases,
    embezzlementState_norm k harmonic]
  norm_num
end QuantumParallelRepetition
