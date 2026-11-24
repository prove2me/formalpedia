-- Prove2me | solution 1 for Psi.validFrom_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:26:05.312844+00:00
-- url     : https://prove2.me/submissions/a6fba1b0-b867-46a7-996d-b835cb061af7

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (h h' : Int) (hle : h ≤ h')
    (hv : validFrom p h) : validFrom p h' := by
  induction p generalizing h h' with
  | nil => trivial
  | cons a t ih => cases a with
    | true => simp only [validFrom] at hv ⊢; exact ih (h + 1) (h' + 1) (by omega) hv
    | false => simp only [validFrom] at hv ⊢; exact ⟨by omega, ih (h - 1) (h' - 1) (by omega) hv.2⟩
end Psi
