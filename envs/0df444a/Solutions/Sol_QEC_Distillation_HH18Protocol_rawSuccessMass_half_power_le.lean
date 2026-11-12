-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.rawSuccessMass_half_power_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:30:52.028007+00:00
-- url     : https://prove2.me/submissions/9d1b70ce-2316-4c24-98aa-f6d29d014ba3

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
    (1 / 2 : ℝ) ^ resourceCount ≤ rawSuccessMass epsilon := by
  calc
    (1 / 2 : ℝ) ^ resourceCount ≤ (1 - epsilon.1) ^ resourceCount := by
      apply pow_le_pow_left₀ (by norm_num)
      linarith [epsilon.property.2]
    _ ≤ rawSuccessMass epsilon := rawSuccessMass_allZeroWord_le epsilon
end QEC.Distillation.HH18Protocol
