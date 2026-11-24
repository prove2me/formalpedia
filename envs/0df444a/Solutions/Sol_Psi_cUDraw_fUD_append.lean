-- Prove2me | solution 1 for Psi.cUDraw_fUD_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:58:17.195773+00:00
-- url     : https://prove2.me/submissions/c488502c-26ec-461b-be9e-ea4abd7c000e

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a : ℕ) (t : List Bool) :
    cUDraw ((List.replicate a [true, false]).flatten ++ t) = a + cUDraw t := by
  induction a with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, List.append_assoc]
      show cUDraw (true :: false :: ((List.replicate n [true, false]).flatten ++ t)) = _
      rw [cUDraw, ih]; omega
end Psi
