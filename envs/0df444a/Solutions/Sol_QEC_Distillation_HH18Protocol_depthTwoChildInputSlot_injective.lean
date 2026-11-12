-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.depthTwoChildInputSlot_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:34:59.505491+00:00
-- url     : https://prove2.me/submissions/1834e782-89a0-42d1-a165-6322ac2514d2

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
import Theorems.Thm_QEC_Distillation_DependentBatch_childInputSlot_injective


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open OneQubitMagic
namespace QEC.Distillation.HH18Protocol
theorem _root_.solution (port : BatchOutputPort) :
    Function.Injective (fun parent : Fin resourceCount =>
      depthTwoRouting (DependentBatch.childInputSlot port parent)) := by
  intro left right hroute
  apply DependentBatch.childInputSlot_injective port
  apply depthTwoRouting.injective
  exact hroute
end QEC.Distillation.HH18Protocol
