-- Prove2me | solution 1 for Psi.validFrom_replicate_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:07:53.650241+00:00
-- url     : https://prove2.me/submissions/945387a2-5da4-4750-928c-8e5f638da7c4

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : ℕ) (h : Int) (hh : (n : Int) ≤ h) :
    validFrom (List.replicate n false) h := by
  induction n generalizing h with
  | zero => simp [validFrom]
  | succ n ih =>
      rw [List.replicate_succ]; simp only [validFrom]
      exact ⟨by push_cast at hh; omega, by apply ih; push_cast at hh ⊢; omega⟩
end Psi
