-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.hh18DepthSchedule_typedPolylogCostBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:51:54.937113+00:00
-- url     : https://prove2.me/submissions/5f980a4a-e021-4b58-84c4-28b2bbb23830

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthSchedule_yield_pos
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthScheduleCostCoefficient_pos
import Theorems.Thm_QEC_Distillation_HH18Protocol_hh18DepthScheduleSuccessfulOutputCost_le_cubicEnvelope_polylog

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
    DependentBatch.typedPolylogCostBound hh18DepthScheduleInputSlots
      hh18DepthScheduleOutputSlots (hh18DepthScheduleTargetError epsilon)
      (hh18DepthScheduleYieldFactor epsilon hsmall)
      hh18DepthScheduleGamma (hh18DepthScheduleCostCoefficient epsilon) := by
  refine ⟨(hh18DepthScheduleCostCoefficient_pos epsilon hepsilon hsmall).le, ?_⟩
  intro depth _ _
  refine ⟨hh18DepthSchedule_yield_pos epsilon hsmall depth, ?_⟩
  exact hh18DepthScheduleSuccessfulOutputCost_le_cubicEnvelope_polylog
    epsilon hepsilon hsmall depth
end QEC.Distillation.HH18Protocol
