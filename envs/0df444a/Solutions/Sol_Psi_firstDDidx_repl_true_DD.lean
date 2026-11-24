-- Prove2me | solution 1 for Psi.firstDDidx_repl_true_DD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:13:42.764408+00:00
-- url     : https://prove2.me/submissions/dc6307fd-a206-43ab-8f05-26d4350780ee

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
import Theorems.Thm_Psi_firstDDidx_true
import Theorems.Thm_Psi_firstDDidx_ff

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (m : ℕ) (r : List Bool) :
    firstDDidx (List.replicate m true ++ false :: false :: r) = some m := by
  induction m with
  | zero => simp [firstDDidx_ff]
  | succ n ih => rw [List.replicate_succ, List.cons_append, firstDDidx_true, ih]; rfl
end Psi
