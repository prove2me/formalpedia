-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthPathStatePackageRate_le_scheduleActualOutputError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:58:59.662246+00:00
-- url     : https://prove2.me/submissions/c3217964-bd1a-4126-b9dc-bf5bbf525668

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathRate_le_scheduleActualOutputError
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathRate_eq_statePackage_rate


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
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    (routedDepthPathStatePackage h hdegree epsilon hsmall depth path).rate.1 ≤
      routedDepthScheduleActualOutputError h hdegree epsilon hsmall depth := by
  rw [← routedDepthPathRate_eq_statePackage_rate h hdegree epsilon hsmall depth path]
  exact routedDepthPathRate_le_scheduleActualOutputError
    h hdegree epsilon hsmall depth path
end QEC.Distillation.HH18Parameterized
