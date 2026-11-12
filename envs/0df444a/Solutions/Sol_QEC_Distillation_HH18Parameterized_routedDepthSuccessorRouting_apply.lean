-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthSuccessorRouting_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:51:40.10713+00:00
-- url     : https://prove2.me/submissions/dd309c2e-1328-4f8a-995c-77d9c1e710a4

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth

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
theorem _root_.solution (m w depth : Nat)
    (pathPrefix : routedDepthOutputSlots m w depth)
    (parent : Fin (physicalInputCount m w)) (port : LogicalSite m w) :
    routedDepthSuccessorRouting m w depth (pathPrefix, (parent, port)) =
      (pathPrefix, (port, parent)) :=
  rfl
end QEC.Distillation.HH18Parameterized
