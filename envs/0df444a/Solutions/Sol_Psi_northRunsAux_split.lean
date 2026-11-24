-- Prove2me | solution 1 for Psi.northRunsAux_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:37:13.369466+00:00
-- url     : https://prove2.me/submissions/79c30c97-2906-4643-86e6-5c490facd6de

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (J : List Bool) (c : ℕ) :
    northRunsAux J c = ppart (c + leadN J) ++ northRuns (afterLeadRun J) := by
  induction J generalizing c with
  | nil => simp [northRunsAux, leadN, afterLeadRun, northRuns, ppart]
  | cons a r ih =>
    cases a with
    | true => simp only [northRunsAux, leadN, afterLeadRun]; rw [ih (c + 1)]; congr 2; omega
    | false => simp only [northRunsAux, leadN, afterLeadRun, northRuns, ppart, add_zero]
end Psi
