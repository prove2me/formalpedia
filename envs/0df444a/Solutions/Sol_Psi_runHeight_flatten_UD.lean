-- Prove2me | solution 1 for Psi.runHeight_flatten_UD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:52:21.667775+00:00
-- url     : https://prove2.me/submissions/cdf2d958-5575-4e9e-a72c-69f68ccbe9ff

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
import Theorems.Thm_Psi_runHeight_append

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (l : ℕ) (h : Int) :
    runHeight ((List.replicate l [true, false]).flatten) h = h := by
  induction l generalizing h with
  | zero => simp [runHeight]
  | succ l ih => rw [List.replicate_succ, List.flatten_cons, runHeight_append]; simp [runHeight, ih]
end Psi
