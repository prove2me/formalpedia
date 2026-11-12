-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthScheduleSuccessfulOutputCost_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:02:31.275693+00:00
-- url     : https://prove2.me/submissions/54684dc6-03c6-4334-b47a-61023219c1fc

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthTypedSuccessfulOutputCost_eq


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
    routedDepthScheduleSuccessfulOutputCost h hdegree epsilon hsmall depth =
      ((physicalInputCount m w : ℝ) / logicalOutputCount m w) ^ depth /
        (routedDepthScheduleExpectedYield h hdegree epsilon hsmall depth : ℝ) :=
  routedDepthTypedSuccessfulOutputCost_eq h hdegree epsilon hsmall depth
end QEC.Distillation.HH18Parameterized
