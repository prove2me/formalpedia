-- Prove2me | solution 1 for Stallings.InverseAutomaton.run_success_of_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:10:39.197524+00:00
-- url     : https://prove2.me/submissions/87f4b9e3-4e42-4e7d-ac2f-b1a9896830b3

import Mathlib.GroupTheory.FreeGroup.Reduce
import Definitions.Def_Stallings_InverseAutomaton
import Theorems.Thm_Stallings_InverseAutomaton_run_success_of_red

set_option autoImplicit true
open Stallings
open Stallings.InverseAutomaton
variable {V : Type*} (G : InverseAutomaton V)
namespace Stallings.InverseAutomaton
theorem _root_.solution (v : V) (w : Word) {t : V}
    (hRun : G.run v w = some t) :
    G.run v (FreeGroup.reduce w) = some t :=
  G.run_success_of_red v (FreeGroup.reduce.red) hRun
end Stallings.InverseAutomaton
