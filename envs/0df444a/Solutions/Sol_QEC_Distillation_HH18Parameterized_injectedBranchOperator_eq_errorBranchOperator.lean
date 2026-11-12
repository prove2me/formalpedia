-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.injectedBranchOperator_eq_errorBranchOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:42:33.186079+00:00
-- url     : https://prove2.me/submissions/ad5f27cb-7de5-416b-91cc-27444ff03c5b

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SitewiseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Syndrome
import Theorems.Thm_QEC_Distillation_HH18Parameterized_sitewiseCorrectedTInvAttempt_rankOne


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
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) (outcomes : InjectionOutcomeWord m w) :
    injectedBranchOperator h error outcomes =
      errorBranchOperator h hdegree error := by
  exact sitewiseCorrectedTInvAttempt_rankOne h hdegree error outcomes
end QEC.Distillation.HH18Parameterized
