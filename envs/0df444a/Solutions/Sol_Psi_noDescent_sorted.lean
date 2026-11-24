-- Prove2me | solution 1 for Psi.noDescent_sorted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:27:22.637451+00:00
-- url     : https://prove2.me/submissions/621cb632-717a-4e23-ace0-623888b88c74

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
import Theorems.Thm_Psi_noDescent_cons_false
import Theorems.Thm_Psi_noDescent_repl_true

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a b : ℕ) :
    noDescent (List.replicate a false ++ List.replicate b true) = true := by
  induction a with
  | zero => simpa using noDescent_repl_true b
  | succ a ih => rw [List.replicate_succ, List.cons_append, noDescent_cons_false]; exact ih
end Psi
