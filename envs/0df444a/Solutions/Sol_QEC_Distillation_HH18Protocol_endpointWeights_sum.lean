-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.endpointWeights_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:15:03.567906+00:00
-- url     : https://prove2.me/submissions/2f2966b9-8a6d-4856-b384-4824e4975733

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceConsumer
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalEndpoint
import Theorems.Thm_QEC_Distillation_HH18Postselection_postselectionWeight_sum


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
attribute [local instance] QEC.Distillation.HH18Protocol.instEndpointClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instEndpointClassicalDecidable
namespace QEC.Distillation.HH18Protocol
theorem _root_.solution
    (inputs : ResourceInput resourceCount QubitSpace) :
    endpointWeight inputs .accepted + endpointWeight inputs .rejected = 1 := by
  exact HH18Postselection.postselectionWeight_sum (resourcePreSyndromeState inputs)
end QEC.Distillation.HH18Protocol
