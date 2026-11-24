-- Prove2me | solution 1 for Psi.validFrom_replicate_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:07:52.834609+00:00
-- url     : https://prove2.me/submissions/39136a8c-e2e0-42dc-9384-b815dadccf32

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : ℕ) (h : Int) :
    validFrom (List.replicate n true) h := by
  induction n generalizing h with
  | zero => simp [validFrom]
  | succ n ih => rw [List.replicate_succ]; simpa [validFrom] using ih (h + 1)
end Psi
