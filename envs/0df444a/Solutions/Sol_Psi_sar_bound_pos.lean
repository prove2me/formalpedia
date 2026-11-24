-- Prove2me | solution 1 for Psi.sar_bound_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:29:26.028816+00:00
-- url     : https://prove2.me/submissions/d5cb9dec-1126-4105-86d6-aa5f24bc8b19

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
import Theorems.Thm_Psi_stEast_nonempty
import Theorems.Thm_Psi_splitAtRow_pos_nil

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (h : Nat) :
    (splitAtRow p h).1 ≠ [] → stEast (splitAtRow p h).1 false = false →
      (splitAtRow p h).2 = [] ∨ (splitAtRow p h).2.head? = some true := by
  fun_induction splitAtRow p h with
  | case1 p => intro hne _; exact absurd rfl hne
  | case2 h => intro hne _; exact absurd rfl hne
  | case3 rest' => intro _ hst; exact absurd hst (by simp [stEast])
  | case4 rest hx =>
      intro _ _
      cases rest with
      | nil => left; rfl
      | cons rh rt => cases rh with
          | true => right; rfl
          | false => exact (hx rt rfl).elim
  | case5 rest h ro ro' heq ihrec =>
      rw [heq] at ihrec
      intro _ hst
      simp only [stEast] at hst
      by_cases hro : ro = []
      · subst hro
        have h0 := splitAtRow_pos_nil rest h (by rw [heq])
        rw [heq, Prod.mk.injEq] at h0
        exact Or.inl h0.2
      · exact ihrec hro hst
  | case6 rest h ro ro' heq ihrec =>
      rw [heq] at ihrec
      intro _ hst
      simp only [stEast] at hst
      by_cases hro : ro = []
      · subst hro; simp [stEast] at hst
      · rw [stEast_nonempty ro hro true false] at hst
        exact ihrec hro hst
end Psi
