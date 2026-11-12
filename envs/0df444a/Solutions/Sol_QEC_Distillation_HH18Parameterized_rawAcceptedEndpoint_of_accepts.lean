-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.rawAcceptedEndpoint_of_accepts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:55:56.245198+00:00
-- url     : https://prove2.me/submissions/8a7e37fd-c642-4a42-85fd-ad744b555d6a

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Syndrome
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Postselection
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_HH18Parameterized_rawSyndromeBranch_eq


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
attribute [local instance 100] Fintype.ofFinite
universe u
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat} (h : Admissible w r m)
    (hdegree : 3 * r < m) (error : PhysicalErrorWord m w)
    (outcomes : InjectionOutcomeWord m w) (haccept : Accepts w r m error) :
    rawAcceptedEndpoint h error outcomes = errorBranchOperator h hdegree error := by
  rw [rawAcceptedEndpoint, rawSyndromeBranch_eq h hdegree]
  exact if_pos haccept.symm
end QEC.Distillation.HH18Parameterized
