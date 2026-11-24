-- Prove2me | solution 1 for Psi.takeWhile_id_head_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:40:42.489819+00:00
-- url     : https://prove2.me/submissions/f94c79bf-6a0e-4886-9af7-e9bb12eacc22

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (L : List Bool) (h : L.head? ≠ some true) :
    (L.takeWhile id).length = 0 := by
  cases L with
  | nil => simp
  | cons y ys =>
      simp only [List.head?_cons, ne_eq, Option.some.injEq] at h
      have : y = false := by cases y <;> simp_all
      subst this; simp
end Psi
