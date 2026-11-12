-- Prove2me | solution 1 for QEC.Distillation.HH18SyndromeDecoding.rawAcceptedEndpoint_of_rejects
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:52:40.37221+00:00
-- url     : https://prove2.me/submissions/c78303f1-7670-4446-929e-09d3007720cf

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SitewisePhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SyndromeDecoding
import Theorems.Thm_QEC_Distillation_HH18SyndromeDecoding_rawSyndromeBranch_eq
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18SyndromeDecoding
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
namespace QEC.Distillation.HH18SyndromeDecoding
theorem _root_.solution
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord)
    (hreject : ¬ Accepts error) :
    rawAcceptedEndpoint error outcomes = 0 := by
  rw [rawAcceptedEndpoint, rawSyndromeBranch_eq]
  exact if_neg (fun heq => hreject heq.symm)
end QEC.Distillation.HH18SyndromeDecoding
