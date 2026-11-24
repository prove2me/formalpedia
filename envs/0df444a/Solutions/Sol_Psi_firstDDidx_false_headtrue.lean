-- Prove2me | solution 1 for Psi.firstDDidx_false_headtrue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:39:37.32083+00:00
-- url     : https://prove2.me/submissions/20affbed-0d5f-4d5e-b4ed-ad946d9e3a57

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
import Theorems.Thm_Psi_firstDDidx_ft

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (L : List Bool) (h : L.head? = some true) :
    firstDDidx (false :: L) = (firstDDidx L).map (· + 1) := by
  cases L with
  | nil => simp at h
  | cons y ys => simp only [List.head?_cons, Option.some.injEq] at h; subst h; rw [firstDDidx_ft]
end Psi
