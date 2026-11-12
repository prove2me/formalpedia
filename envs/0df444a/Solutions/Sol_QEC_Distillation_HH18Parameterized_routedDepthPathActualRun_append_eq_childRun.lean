-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthPathActualRun_append_eq_childRun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:57:42.651223+00:00
-- url     : https://prove2.me/submissions/0efc2efb-6db3-4a56-8770-24566a34e0d7

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathActualRun_eq_resourceDecodedRun
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathRate_append_eq_nextInputRate
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthChildRun_eq_resourceDecodedRun


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
    {depth : Nat} (path : routedDepthOutputSlots m w depth)
    (port : LogicalSite m w) :
    routedDepthPathActualRun h hdegree epsilon hsmall (depth + 1)
      (routedDepthOutputPathAppend m w depth path port) =
      routedDepthChildRun h hdegree
        (routedDepthPathState h hdegree epsilon hsmall depth path) port
        (routedDepthPathNextHalf h hdegree epsilon hsmall path port) := by
  rw [routedDepthPathActualRun_eq_resourceDecodedRun,
    routedDepthChildRun_eq_resourceDecodedRun,
    routedDepthPathRate_append_eq_nextInputRate]
end QEC.Distillation.HH18Parameterized
