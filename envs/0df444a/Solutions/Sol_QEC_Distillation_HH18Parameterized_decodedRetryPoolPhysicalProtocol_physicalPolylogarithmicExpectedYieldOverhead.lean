-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocol_physicalPolylogarithmicExpectedYieldOverhead
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:04:55.133914+00:00
-- url     : https://prove2.me/submissions/742c0dc7-7018-4665-8eea-2d3dfc3fca81

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Accounting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthSchedule_physicalPolylogarithmicExpectedYieldOverhead


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
      (routedDepthScheduleInputSlots m w)
      (routedDepthScheduleOutputSlots m w)
      (routedDepthScheduleTargetError w r m epsilon)
      (routedDepthScheduleActualOutputError h hdegree epsilon hsmall)
      (routedDepthScheduleExpectedYield h hdegree epsilon hsmall)
      (routedDepthScheduleGamma w r m)
      (routedDepthScheduleCostCoefficient h epsilon) :=
  routedDepthSchedule_physicalPolylogarithmicExpectedYieldOverhead
    h hdegree epsilon hepsilon hsmall
end QEC.Distillation.HH18Parameterized
