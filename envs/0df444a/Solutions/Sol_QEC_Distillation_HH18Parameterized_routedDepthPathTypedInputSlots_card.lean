-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthPathTypedInputSlots_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:04:54.412015+00:00
-- url     : https://prove2.me/submissions/82f93313-ca48-4ade-bc76-b72d3508f29b

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthInputSlots_card


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
    Fintype.card (routedDepthInputSlots m w depth) =
      physicalInputCount m w ^ depth :=
  routedDepthInputSlots_card m w depth
end QEC.Distillation.HH18Parameterized
