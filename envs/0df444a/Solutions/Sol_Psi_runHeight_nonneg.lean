-- Prove2me | solution 1 for Psi.runHeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:08:00.187307+00:00
-- url     : https://prove2.me/submissions/e5f4b374-0c21-40fe-81bf-0d6f5f64d92e

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (h : Int) (hh : 0 ≤ h)
    (hv : validFrom p h) : 0 ≤ runHeight p h := by
  induction p generalizing h with
  | nil => simpa [runHeight] using hh
  | cons a t ih => cases a with
    | true => simp only [runHeight, validFrom] at hv ⊢; exact ih (h + 1) (by omega) hv
    | false => simp only [runHeight, validFrom] at hv ⊢; exact ih (h - 1) (by omega) hv.2
end Psi
