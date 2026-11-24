-- Prove2me | solution 1 for Psi.split_numN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:57:52.912694+00:00
-- url     : https://prove2.me/submissions/4673012b-8a49-448d-a595-2c12a60d9645

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_numN_cons_true
import Theorems.Thm_Psi_numN_cons_false

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (pi : List Bool) (h : ℕ) (hh : h ≤ numN pi) :
    numN (splitAtRow pi h).1 = h := by
  fun_induction splitAtRow pi h with
  | case1 p => simp [numN]
  | case2 h => simp only [numN, List.filter_nil, List.length_nil] at hh ⊢; omega
  | case3 rest' => simp [numN]
  | case4 rest hx => simp [numN]
  | case5 rest h ro ro' heq ih =>
      rw [numN_cons_true] at hh; rw [heq] at ih; simp only at ih
      rw [numN_cons_true, ih (by omega)]
  | case6 rest h ro ro' heq ih =>
      rw [numN_cons_false] at hh; rw [heq] at ih; simp only at ih
      rw [numN_cons_false]; exact ih hh
end Psi
