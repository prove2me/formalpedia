-- Prove2me | solution 1 for ReciprocityTheory.Coh.shift_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:45:32.126923+00:00
-- url     : https://prove2.me/submissions/901b437b-0f04-4db5-a0f2-355f76d55d8d

import Definitions.Def_ReciprocityTheory_GroupCohomology_CardLenStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_GroupCohomology_ShiftA
import Definitions.Def_ReciprocityTheory_GroupCohomology_KilledHolds
import Theorems.Thm_ReciprocityTheory_Coh_KernelCokernelKilling_shQ_tors
import Theorems.Thm_ReciprocityTheory_Coh_KernelCokernelKilling_shift_step


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
open KernelCokernelKilling
namespace ReciprocityTheory.Coh
theorem _root_.solution : ShiftStatement.{u} := by
  intro R _ G _ _ _ _ N hN M _ hM n hn
  induction n, hn using Nat.le_induction generalizing M with
  | base => exact hN M hM
  | succ n hNn ih =>
    exact KernelCokernelKilling.shift_step M n (ih (KernelCokernelKilling.shQ M) (KernelCokernelKilling.shQ_tors M hM))
end ReciprocityTheory.Coh
