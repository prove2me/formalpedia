-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.codeDistance_semanticDistance
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T19:28:24.601518+00:00
-- url     : https://prove2.me/submissions/cf77c4c0-ecc1-401b-b6d1-ae3f102bc6a3

import Theorems.Thm_QEC_Distillation_HH18PuncturedReedMuller_semanticDistance
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Types
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
attribute [local instance 100] Fintype.ofFinite

theorem solution {w r m : Nat} (h : Admissible w r m) :
    StabilizerCode.SemanticStabilizerDistance
      (HH18PuncturedReedMuller.sourceValidStabilizer h) (codeDistance r w) := by
  simpa only [codeDistance] using HH18PuncturedReedMuller.semanticDistance h