-- Prove2me | solution 1 for QEC.Distillation.BK05T.fiveQubitAcceptedConditionalBeforeSwap_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-17T19:43:06.530166+00:00
-- url     : https://prove2.me/submissions/17fb433d-8ac2-4701-a4d1-563609fffa7d

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator



set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSimpArgs false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open OneQubitMagic
open scoped BigOperators ComplexOrder TensorProduct
attribute [local irreducible] fiveQubitPreparedRowScalar
attribute [local irreducible] GaussianInt.toComplex
attribute [local irreducible] arrayTarget
namespace QEC.Distillation.BK05T
theorem _root_.solution
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    (fiveQubitAcceptedConditionalBeforeSwap epsilon hzero hone).toOperator =
      ((fiveQubitSuccessProbability epsilon : Complex)⁻¹) •
        ((fiveQubitRawTZeroCoefficient epsilon : Complex) • tZero.toOperator +
          (fiveQubitRawTOneCoefficient epsilon : Complex) •
            tOne.toOperator) := by
  rw [fiveQubitAcceptedConditionalBeforeSwap,
    FiniteInstrument.conditionalDensity_toOperator,
    fiveQubitAcceptedBornWeight_eq_success]
  change
    ((fiveQubitSuccessProbability epsilon : Complex)⁻¹) •
        fiveQubitDecodedAcceptedRaw epsilon hzero hone = _
  rw [fiveQubitDecodedAcceptedRaw_eq]
end QEC.Distillation.BK05T
