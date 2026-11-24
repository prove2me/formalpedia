-- Prove2me | solution 1 for Psi.muVecAux_head_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:37:02.438404+00:00
-- url     : https://prove2.me/submissions/8b553896-86ae-413e-ada1-8827e6c79d26

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (L : List ℕ) (hpt : ℕ) (hL : 0 < L.headD 0) :
    muVecAux L hpt = ppart (L.headD 0 - hpt) ++ (muVec L).tail := by
  cases L with
  | nil => simp at hL
  | cons x xs =>
    simp only [List.headD_cons] at hL
    have hmv : muVec (x :: xs) = x :: muVecAux xs x := by
      simp only [muVec, muVecAux, Nat.sub_zero]; rw [if_pos hL, List.singleton_append]
    rw [hmv]
    simp [muVecAux, ppart]
end Psi
