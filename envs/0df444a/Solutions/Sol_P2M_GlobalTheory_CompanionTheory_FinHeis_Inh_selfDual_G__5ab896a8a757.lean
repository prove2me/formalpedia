-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_FinHeis_Inh_selfDual_G__5ab896a8a757
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:53:14.114716+00:00
-- url     : https://prove2.me/submissions/22691b07-8691-4748-8c5e-1c7284fe1826

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Inh_e_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinHeis
variable {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (S : Sys X M)
variable {S}
open GlobalTheory.CompanionTheory.FinHeis.Inh
namespace GlobalTheory.CompanionTheory.FinHeis.Inh
theorem _root_.solution : SelfDual sysEx G₁ := by
  intro x
  simp only [mem_G₁, sysEx, e_sq]
  revert x; decide
end GlobalTheory.CompanionTheory.FinHeis.Inh
