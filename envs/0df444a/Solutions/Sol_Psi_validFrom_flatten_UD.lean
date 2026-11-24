-- Prove2me | solution 1 for Psi.validFrom_flatten_UD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:08:03.601875+00:00
-- url     : https://prove2.me/submissions/125eedec-f41c-4bc1-80e3-be9c0099c248

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
import Theorems.Thm_Psi_validFrom_append

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (l : ℕ) (h : Int) (hh : 0 ≤ h) :
    validFrom ((List.replicate l [true, false]).flatten) h := by
  induction l generalizing h with
  | zero => simp [validFrom]
  | succ l ih =>
      rw [List.replicate_succ, List.flatten_cons, validFrom_append]
      exact ⟨⟨by omega, trivial⟩, by
        rw [show runHeight [true, false] h = h from by simp [runHeight]]; exact ih h hh⟩
end Psi
