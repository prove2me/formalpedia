-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthScheduleOutputSlots_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:52:32.910116+00:00
-- url     : https://prove2.me/submissions/c7a7d5cc-c596-4700-9a7f-c7cb8dc20cc9

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathTypedOutputSlots_card


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
theorem _root_.solution (m w depth : Nat) :
    Fintype.card (routedDepthScheduleOutputSlots m w depth) =
      logicalOutputCount m w ^ depth :=
  routedDepthPathTypedOutputSlots_card m w depth
end QEC.Distillation.HH18Parameterized
