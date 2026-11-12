-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolAcceptedPortSuccessorConditionalDensity_eq_acceptedProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:23:08.588012+00:00
-- url     : https://prove2.me/submissions/3507b3da-982c-468c-b68a-3f6e1e272c34

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedPortRecordProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_MeasuredRecordProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Routing
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolAcceptedPortSuccessorInputChannel_mapDensity
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolAcceptedPortSuccessorBornWeight_eq_tensorPowerBornProduct
import Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_JointMeasurement_conditionalDensity_toOperator
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPool_enoughBranch_eq_bornProduct_smul_acceptedProduct
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
attribute [local simp] QEC.Distillation.AdaptiveIdealClifford.JointMeasurement.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open Triorthogonal.BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (hhalf : selectedLogicalPortRawError h hdegree epsilon port ≤ 1 / 2)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (history : tensorPowerHistory DistillationOutcome
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩))
    (henough :
      decodedRetryPoolBackwardSchedule m w z q
          ⟨stage.1 + 1, hstage⟩ ≤
        (tensorPowerAcceptedIndices decodedRetryPoolAccepts
          (decodedRetryPoolBackwardAttempts m w z q
            ⟨stage.1 + 1, hstage⟩) history).card)
    (hpositive : 0 <
      decodedRetryPoolAcceptedPortSuccessorBornWeight
        h hdegree epsilon z q stage hstage port hhalf rhoUnit history) :
    (decodedRetryPoolInstrument h hdegree
      (decodedRetryPoolBackwardAttempts m w z q
        ⟨stage.1 + 1, hstage⟩)
      (decodedRetryPoolBackwardSchedule m w z q
        ⟨stage.1 + 1, hstage⟩)).conditionalDensity
        ⟨history, PUnit.unit⟩
        ((decodedRetryPoolAcceptedPortSuccessorInputChannel
          m w z q stage hstage port).mapDensity
            (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
              (decodedRetryPoolBackwardSchedule m w z q stage)))
        hpositive =
      decodedRetryPoolAcceptedProductDensity h hdegree
        (selectedLogicalPortNextInputRate h hdegree epsilon port hhalf)
        rhoUnit
        (decodedRetryPoolBackwardSchedule m w z q
          ⟨stage.1 + 1, hstage⟩) := by
  let attempts :=
    decodedRetryPoolBackwardAttempts m w z q
      ⟨stage.1 + 1, hstage⟩
  let required :=
    decodedRetryPoolBackwardSchedule m w z q
      ⟨stage.1 + 1, hstage⟩
  let nextRate :=
    selectedLogicalPortNextInputRate h hdegree epsilon port hhalf
  have hinput :=
    decodedRetryPoolAcceptedPortSuccessorInputChannel_mapDensity
      h hdegree epsilon z q stage hstage port hhalf rhoUnit
  have hbranch :=
    decodedRetryPool_enoughBranch_eq_bornProduct_smul_acceptedProduct
      h hdegree nextRate rhoUnit attempts required history henough
  have hweight :=
    decodedRetryPoolAcceptedPortSuccessorBornWeight_eq_tensorPowerBornProduct
      h hdegree epsilon z q stage hstage port hhalf rhoUnit history
  apply DensityOperator.ext_toOperator
  erw [FiniteInstrument.conditionalDensity_toOperator]
  change
    ((decodedRetryPoolAcceptedPortSuccessorBornWeight
      h hdegree epsilon z q stage hstage port hhalf rhoUnit history : Complex)⁻¹) •
      (decodedRetryPoolInstrument h hdegree attempts required).branchOperator
        ⟨history, PUnit.unit⟩
        ((decodedRetryPoolAcceptedPortSuccessorInputChannel
          m w z q stage hstage port).mapDensity
            (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
              (decodedRetryPoolBackwardSchedule m w z q stage))).toOperator = _
  rw [hinput]
  rw [hbranch]
  rw [hweight]
  rw [← mul_smul]
  rw [inv_mul_cancel₀]
  · change (1 : Complex) •
        (decodedRetryPoolAcceptedProductDensity h hdegree nextRate rhoUnit
          required).toOperator = _
    rw [one_smul]
  · exact_mod_cast (hweight ▸ ne_of_gt hpositive)
end QEC.Distillation.HH18Parameterized
