-- Prove2me | solution 1 for QEC.Distillation.HH18SyndromeDecoding.injectedBranchOperator_eq_errorBranchOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:33:51.730608+00:00
-- url     : https://prove2.me/submissions/c22a0b18-a15a-4396-b879-0feeb4683419

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SitewisePhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SyndromeDecoding
import Theorems.Thm_QEC_Distillation_HH18SitewisePhaseInjection_sitewiseCorrectedTInvAttempt_rankOne


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
    (error : PhysicalErrorWord) (outcomes : InjectionOutcomeWord) :
    injectedBranchOperator error outcomes = errorBranchOperator error := by
  exact HH18SitewisePhaseInjection.sitewiseCorrectedTInvAttempt_rankOne
    error outcomes
end QEC.Distillation.HH18SyndromeDecoding
