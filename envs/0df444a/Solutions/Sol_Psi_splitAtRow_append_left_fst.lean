-- Prove2me | solution 1 for Psi.splitAtRow_append_left_fst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:30:44.809542+00:00
-- url     : https://prove2.me/submissions/c5ce1287-57d3-43ca-bfff-8164057c8732

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_numN_cons_true
import Theorems.Thm_Psi_numN_cons_false
import Theorems.Thm_Psi_stEast_nonempty


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (B C : List Bool) (h : ℕ)
    (hend : stEast B false = true) (hh : h ≤ numN B) :
    (splitAtRow (B ++ C) h).1 = (splitAtRow B h).1 := by
  fun_induction splitAtRow B h with
  | case1 p => simp [splitAtRow]
  | case2 h => simp [stEast] at hend
  | case3 rest' => simp only [List.cons_append, splitAtRow]
  | case4 rest hx =>
      cases rest with
      | nil => simp [stEast] at hend
      | cons b rt => cases b with
        | false => exact (hx rt rfl).elim
        | true => simp only [List.cons_append, splitAtRow]
  | case5 rest h ro ro' heq ih =>
      simp only [List.cons_append, splitAtRow]
      have hst : stEast rest false = true := hend
      have hnn : h + 1 ≤ numN rest := by rw [numN_cons_true] at hh; omega
      congr 1
      have := ih hst hnn; rw [heq] at this; simpa using this
  | case6 rest h ro ro' heq ih =>
      simp only [List.cons_append, splitAtRow]
      have hrne : rest ≠ [] := by
        rw [numN_cons_false] at hh; intro h0; subst h0; simp [numN] at hh
      have hst : stEast rest false = true := by
        have h1 : stEast rest true = true := hend
        rwa [stEast_nonempty rest hrne true false] at h1
      have hnn : h + 1 ≤ numN rest := by rw [numN_cons_false] at hh; exact hh
      congr 1
      have := ih hst hnn; rw [heq] at this; simpa using this
end Psi
