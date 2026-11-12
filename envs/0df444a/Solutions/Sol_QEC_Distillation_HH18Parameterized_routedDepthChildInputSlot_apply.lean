-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthChildInputSlot_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:52:00.899207+00:00
-- url     : https://prove2.me/submissions/ca974d96-fe76-4e51-b20a-12dd0a6bdace

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
    (pathPrefix : routedDepthOutputSlots m w depth) (child : LogicalSite m w)
    (parent : Fin (physicalInputCount m w)) :
    routedDepthChildInputSlot m w depth pathPrefix child parent =
      (pathPrefix, (child, parent)) :=
  rfl
end QEC.Distillation.HH18Parameterized
