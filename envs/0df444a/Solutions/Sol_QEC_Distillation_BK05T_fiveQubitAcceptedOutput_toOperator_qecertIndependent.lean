-- Prove2me | solution 1 for QEC.Distillation.BK05T.fiveQubitAcceptedOutput_toOperator_qecertIndependent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:59:47.634087+00:00
-- url     : https://prove2.me/submissions/8ea4f208-6c35-41ce-9b15-c011cc2fd1c5

import Definitions.Def_QECert_BK05T_AcceptedOutputIndependent
set_option autoImplicit false
noncomputable section
open QEC.Semantics
open QEC.Distillation.BK05T.QECertAcceptedOutputIndependent
open scoped BigOperators ComplexOrder TensorProduct
theorem _root_.solution
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    (fiveQubitAcceptedOutput epsilon hzero hone).toOperator =
      ((fiveQubitRawTOneCoefficient epsilon /
          fiveQubitSuccessProbability epsilon : Real) : Complex) •
        tZero.toOperator +
      ((fiveQubitRawTZeroCoefficient epsilon /
          fiveQubitSuccessProbability epsilon : Real) : Complex) •
        tOne.toOperator := by
  rw [fiveQubitAcceptedOutput]
  change QEC.Semantics.DensityOperator.convexCombinationOperator Finset.univ
    (fiveQubitAcceptedOutputWeight epsilon) tInputComponent = _
  simp [DensityOperator.convexCombinationOperator,
    fiveQubitAcceptedOutputWeight, tInputComponent]
  simp only [RCLike.real_smul_eq_coe_smul (K := Complex)]
  norm_num
