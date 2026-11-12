-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthSchedule_typedPolylogCostBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:32:14.993396+00:00
-- url     : https://prove2.me/submissions/928e0514-659a-46de-8ea2-cf8fdb8ab1b5

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleExpectedYield_pos
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleCostCoefficient_pos
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleSuccessfulOutputCost_le_polylog

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    DependentBatch.typedPolylogCostBound
      (routedDepthScheduleInputSlots m w)
      (routedDepthScheduleOutputSlots m w)
      (routedDepthScheduleTargetError w r m epsilon)
      (routedDepthScheduleExpectedYield h hdegree epsilon hsmall)
      (routedDepthScheduleGamma w r m)
      (routedDepthScheduleCostCoefficient h epsilon) := by
  refine ⟨(routedDepthScheduleCostCoefficient_pos h epsilon hepsilon hsmall).le,
    ?_⟩
  intro depth _ _
  refine ⟨routedDepthScheduleExpectedYield_pos h hdegree epsilon hsmall depth,
    ?_⟩
  exact routedDepthScheduleSuccessfulOutputCost_le_polylog h hdegree epsilon
    hepsilon hsmall depth
end QEC.Distillation.HH18Parameterized
