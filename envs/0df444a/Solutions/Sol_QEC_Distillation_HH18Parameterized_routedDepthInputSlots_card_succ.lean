-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthInputSlots_card_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:51:48.789577+00:00
-- url     : https://prove2.me/submissions/d02110b9-f086-4367-bba9-c8f1771c7e5a

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
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
    Fintype.card (routedDepthInputSlots m w (depth + 1)) =
      Fintype.card (routedDepthInputSlots m w depth) * physicalInputCount m w := by
  rw [routedDepthInputSlots_card, routedDepthInputSlots_card]
  exact pow_succ _ _
end QEC.Distillation.HH18Parameterized
