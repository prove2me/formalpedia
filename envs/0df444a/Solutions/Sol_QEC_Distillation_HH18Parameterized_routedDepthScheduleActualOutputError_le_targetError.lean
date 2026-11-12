-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthScheduleActualOutputError_le_targetError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:54:57.283461+00:00
-- url     : https://prove2.me/submissions/70cadd48-256c-40ff-bf67-e891fb907a5e

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthErrorEnvelope_le_scheduleTargetError
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathRate_le_errorEnvelope


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
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    routedDepthScheduleActualOutputError h hdegree epsilon hsmall depth ≤
      routedDepthScheduleTargetError w r m epsilon depth := by
  classical
  calc
    routedDepthScheduleActualOutputError h hdegree epsilon hsmall depth ≤
        routedDepthErrorEnvelope w r m epsilon depth := by
      unfold routedDepthScheduleActualOutputError
      apply Finset.sup'_le
      intro path _
      exact routedDepthPathRate_le_errorEnvelope h hdegree epsilon hsmall depth path
    _ ≤ routedDepthScheduleTargetError w r m epsilon depth :=
      routedDepthErrorEnvelope_le_scheduleTargetError h epsilon depth
end QEC.Distillation.HH18Parameterized
