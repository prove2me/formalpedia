-- Prove2me | solution 1 for Stallings.InverseAutomaton.run_success_of_red_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:08:51.824885+00:00
-- url     : https://prove2.me/submissions/00d885b5-14f0-4fc8-b8f7-8b4e9560c817

import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Stallings_InverseAutomaton
import Theorems.Thm_Stallings_InverseAutomaton_run_success_cancel

set_option autoImplicit true
open Stallings
open Stallings.InverseAutomaton
variable {V : Type*} (G : InverseAutomaton V)
namespace Stallings.InverseAutomaton
theorem _root_.solution (v : V) {w z : Word}
    (h : FreeGroup.Red.Step w z) {t : V}
    (hRun : G.run v w = some t) : G.run v z = some t := by
  cases h with
  | not => exact G.run_success_cancel v _ _ _ hRun
end Stallings.InverseAutomaton
