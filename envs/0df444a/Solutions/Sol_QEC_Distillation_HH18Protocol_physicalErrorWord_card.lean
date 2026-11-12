-- Prove2me | solution 1 for QEC.Distillation.HH18Protocol.physicalErrorWord_card
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T18:28:44.819184+00:00
-- url     : https://prove2.me/submissions/932500f7-d33e-4cd0-8b8d-e24e9b8b3bac

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_ResourceConsumer
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhysicalEndpoint
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

theorem solution : Fintype.card PhysicalErrorWord = 2 ^ resourceCount := by
  simp [PhysicalErrorWord, HH18NoisyInput.PhysicalErrorWord, resourceCount]