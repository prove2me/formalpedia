-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthSchedule_physicalPolylogarithmicExpectedYieldOverhead
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:35:44.967825+00:00
-- url     : https://prove2.me/submissions/18f2fd09-cc48-4b5a-86b2-ceadc4616fd3

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleActualOutputError_le_targetError
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthSchedule_typedPolylogCostBound

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
      (routedDepthScheduleCostCoefficient h epsilon) := by
  rcases routedDepthSchedule_typedPolylogCostBound h hdegree epsilon hepsilon
    hsmall with ⟨hcoefficient, hcost⟩
  refine ⟨hcoefficient, ?_⟩
  intro depth htargetPos htargetLtOne
  obtain ⟨hyield, hcostBound⟩ := hcost depth htargetPos htargetLtOne
  exact ⟨routedDepthScheduleActualOutputError_le_targetError h hdegree epsilon
    hsmall depth, hyield, hcostBound⟩
end QEC.Distillation.HH18Parameterized
