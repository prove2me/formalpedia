-- Prove2me | solution 1 for Stallings.InverseAutomaton.run_success_of_red
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:09:55.771338+00:00
-- url     : https://prove2.me/submissions/6a5a8a7e-5037-40b8-9f5d-acfd8ae59893

import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Stallings_InverseAutomaton
import Theorems.Thm_Stallings_InverseAutomaton_run_success_of_red_step

set_option autoImplicit true
open Stallings
open Stallings.InverseAutomaton
variable {V : Type*} (G : InverseAutomaton V)
namespace Stallings.InverseAutomaton
theorem _root_.solution (v : V) {w z : Word}
    (h : FreeGroup.Red w z) {t : V}
    (hRun : G.run v w = some t) : G.run v z = some t := by
  induction h generalizing t hRun with
  | refl => exact hRun
  | tail hred hstep ih =>
      exact G.run_success_of_red_step v hstep (ih hRun)
end Stallings.InverseAutomaton
