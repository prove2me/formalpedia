-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.rawSuccessMass_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:28:38.705324+00:00
-- url     : https://prove2.me/submissions/181e7bea-4930-4370-b049-b6b85eb15e59

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceConsumer
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalEndpoint
import Theorems.Thm_QEC_Distillation_HH18Protocol_rawSuccessMass_allZeroWord_le

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
    0 < rawSuccessMass epsilon := by
  have hfactor : 0 < 1 - epsilon.1 := by
    linarith [epsilon.property.2]
  exact lt_of_lt_of_le (pow_pos hfactor _) (rawSuccessMass_allZeroWord_le epsilon)
end QEC.Distillation.HH18Protocol
