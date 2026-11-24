-- Prove2me | solution 1 for Psi.cUDraw_true_head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:39:35.439044+00:00
-- url     : https://prove2.me/submissions/42791f86-ba45-47fe-a5ec-68bbb143c263

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (L : List Bool) (h : L.head? = some true) :
    cUDraw (true :: L) = 0 := by
  cases L with
  | nil => simp at h
  | cons y ys => simp only [List.head?_cons, Option.some.injEq] at h; subst h; rfl
end Psi
