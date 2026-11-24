-- Prove2me | solution 1 for Psi.muVec_headD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:38:48.254693+00:00
-- url     : https://prove2.me/submissions/e50e07f3-07a9-41b3-85df-e0bfc735eb91

import Definitions.Def_RequestProject_Psi_Area
import Definitions.Def_RequestProject_Psi_RiseComp

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (L : List ℕ) (hL : 0 < L.headD 0) :
    (muVec L).headD 0 = L.headD 0 := by
  cases L with
  | nil => simp at hL
  | cons x xs =>
    simp only [List.headD_cons] at hL
    have hmv : muVec (x :: xs) = x :: muVecAux xs x := by
      simp only [muVec, muVecAux, Nat.sub_zero]; rw [if_pos hL, List.singleton_append]
    rw [hmv]; simp
end Psi
