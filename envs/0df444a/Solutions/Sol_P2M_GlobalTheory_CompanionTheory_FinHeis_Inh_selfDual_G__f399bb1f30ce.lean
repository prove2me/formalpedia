-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_FinHeis_Inh_selfDual_G__f399bb1f30ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:50:31.339807+00:00
-- url     : https://prove2.me/submissions/40fec5a2-5104-4403-9094-151839dc515f

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
theorem _root_.solution : SelfDual sysEx G₂ := by
  intro x
  simp only [mem_G₂, sysEx, e_sq]
  revert x; decide
end GlobalTheory.CompanionTheory.FinHeis.Inh
