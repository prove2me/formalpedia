-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatch_physicalPolylogarithmicExpectedYieldOverhead
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:14:59.177011+00:00
-- url     : https://prove2.me/submissions/4025117d-d79a-4cd4-ad27-dafbb053f916

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Cost
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Asymptotic
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalExactBatchYield_pos
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient_pos
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalExactBatchSuccessfulOutputCost_le_polylog

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
      (decodedRetryPoolPhysicalExactBatchInputSlots m w)
      (decodedRetryPoolPhysicalExactBatchOutputSlots m w)
      (fun depth =>
        routedDepthScheduleTargetError w r m epsilon (depth + 1))
      (fun depth => decodedRetryPoolPhysicalExactBatchActualOutputError
        h hdegree epsilon depth rhoUnit)
      (fun depth => decodedRetryPoolPhysicalExactBatchYield
        h hdegree epsilon depth rhoUnit)
      (routedDepthScheduleGamma w r m)
      (decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient h epsilon) := by
  refine
    ⟨(decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient_pos
      h epsilon hepsilon hpool).le, ?_⟩
  intro depth _ _
  exact
    ⟨decodedRetryPoolPhysicalExactBatchActualOutputError_le_targetError
      h hdegree epsilon hpool depth rhoUnit,
    decodedRetryPoolPhysicalExactBatchYield_pos
      h hdegree epsilon hpool depth rhoUnit,
    decodedRetryPoolPhysicalExactBatchSuccessfulOutputCost_le_polylog
      h hdegree epsilon hepsilon hpool depth rhoUnit⟩
end QEC.Distillation.HH18Parameterized
