-- Prove2me | solution 1 for QEC.Distillation.BK05T.fiveQubitDistillationRun_acceptedOutput
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T21:25:48.536+00:00
-- url     : https://prove2.me/submissions/404d18a7-000d-4a4c-a2d9-ea00c7c24557

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
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

theorem solution
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    (fiveQubitDistillationRun epsilon hzero hone).acceptedOutput =
      fiveQubitAcceptedOutput epsilon hzero hone := by
  apply qubitDensityOperator_ext
  change fiveQubitOutputSwapChannel.toLinearMap
      (fiveQubitAcceptedConditionalBeforeSwap epsilon hzero hone).toOperator = _
  have hc : (fiveQubitAcceptedConditionalBeforeSwap epsilon hzero hone).toOperator =
      ((fiveQubitSuccessProbability epsilon : Complex)⁻¹) •
        fiveQubitDecodedAcceptedRaw epsilon hzero hone := by
    change ((fiveQubitDecodingInstrument.bornWeight .accepted
        (fiveQubitPrepareInput (fiveQubitNoisyResources epsilon hzero hone)) : Complex)⁻¹) • _ = _
    rw [fiveQubitAcceptedBornWeight_eq_success]
    rfl
  have h0' : fiveQubitOutputSwapChannel.toLinearMap tZero.toOperator = tOne.toOperator :=
    congrArg DensityOperator.toOperator fiveQubitOutputSwapChannel_tZero
  have h1' : fiveQubitOutputSwapChannel.toLinearMap tOne.toOperator = tZero.toOperator :=
    congrArg DensityOperator.toOperator fiveQubitOutputSwapChannel_tOne
  rw [hc, fiveQubitDecodedAcceptedRaw_eq, map_smul, map_add, map_smul, map_smul, h0', h1']
  change _ = ∑ i ∈ Finset.univ, ((fiveQubitAcceptedOutputWeight epsilon i : ℝ) : Complex) •
    (tInputComponent i).toOperator
  rw [Fin.sum_univ_two]
  simp only [fiveQubitAcceptedOutputWeight, tInputComponent]
  push_cast
  rw [smul_add, smul_smul, smul_smul, add_comm]
  congr 1 <;> congr 1 <;> ring
