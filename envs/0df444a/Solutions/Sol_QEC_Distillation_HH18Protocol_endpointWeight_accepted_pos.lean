-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.endpointWeight_accepted_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:08:04.275201+00:00
-- url     : https://prove2.me/submissions/9c669d93-1894-4bde-9866-787f909738b5

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceConsumer
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalEndpoint
import Theorems.Thm_QEC_Distillation_HH18Protocol_endpointWeight_accepted_eq_rawSuccessMass
import Theorems.Thm_QEC_Distillation_HH18Protocol_rawSuccessMass_pos

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
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    0 < endpointWeight (noisyResources epsilon) .accepted := by
  rw [endpointWeight_accepted_eq_rawSuccessMass]
  exact rawSuccessMass_pos epsilon
end QEC.Distillation.HH18Protocol
