-- Prove2me | solution 1 for Psi.takeWhile_false_head_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:40:51.835503+00:00
-- url     : https://prove2.me/submissions/b50346c8-fe7c-422b-a960-fde31ada5632

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (L : List Bool) (h : L.head? ≠ some false) :
    (L.takeWhile (· = false)).length = 0 := by
  cases L with
  | nil => simp
  | cons y ys =>
      simp only [List.head?_cons, ne_eq, Option.some.injEq] at h
      have : y = true := by cases y <;> simp_all
      subst this; simp
end Psi
