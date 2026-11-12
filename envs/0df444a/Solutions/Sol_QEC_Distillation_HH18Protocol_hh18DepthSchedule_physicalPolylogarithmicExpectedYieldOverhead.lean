-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18DepthSchedule_physicalPolylogarithmicExpectedYieldOverhead
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:36:44.190586+00:00
-- url     : https://prove2.me/submissions/49e83cae-5e61-4eb7-9fd2-6c79cad59a68

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthSchedule_actualOutputError_le_targetError
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthSchedule_typedPolylogCostBound

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open OneQubitMagic
namespace QEC.Distillation.HH18Protocol
theorem _root_.solution
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : hh18InitialSmallDomain epsilon) :
    DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
      hh18DepthScheduleInputSlots hh18DepthScheduleOutputSlots
      (hh18DepthScheduleTargetError epsilon)
      (hh18DepthScheduleActualOutputError epsilon hsmall)
      (hh18DepthScheduleYieldFactor epsilon hsmall)
      hh18DepthScheduleGamma (hh18DepthScheduleCostCoefficient epsilon) := by
  rcases hh18DepthSchedule_typedPolylogCostBound epsilon hepsilon hsmall with
    ⟨hcoefficient, hcost⟩
  refine ⟨hcoefficient, ?_⟩
  intro depth htargetPos htargetLtOne
  obtain ⟨hyield, hcostBound⟩ := hcost depth htargetPos htargetLtOne
  exact ⟨hh18DepthSchedule_actualOutputError_le_targetError epsilon hsmall depth,
    hyield, hcostBound⟩
end QEC.Distillation.HH18Protocol
