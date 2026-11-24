-- Prove2me | solution 1 for Psi.numN_le_numNBeforeDD_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:47:22.998276+00:00
-- url     : https://prove2.me/submissions/4787cc8a-fa57-449f-a535-d1ed78121ef5

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
import Theorems.Thm_Psi_numNBeforeDD_cons_true
import Theorems.Thm_Psi_hasDD_cons
import Theorems.Thm_Psi_numN_cons_false
import Theorems.Thm_Psi_numN_cons_true


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (ρ ρ' : List Bool) (hρDD : hasDD ρ = false) :
    numN ρ ≤ numNBeforeDD (ρ ++ ρ') := by
  induction ρ with
  | nil => simp [numN]
  | cons x xs ih =>
    cases x with
    | true =>
      have hxs : hasDD xs = false := by rw [hasDD_cons] at hρDD; exact (Bool.or_eq_false_iff.mp hρDD).2
      simp only [List.cons_append, numNBeforeDD_cons_true, numN_cons_true]
      have := ih hxs; omega
    | false =>
      rw [numN_cons_false, List.cons_append]
      cases xs with
      | nil => simp [numN]
      | cons y ys =>
        cases y with
        | false => simp [hasDD] at hρDD
        | true =>
          have hxs : hasDD (true :: ys) = false := by
            rw [hasDD_cons] at hρDD; exact (Bool.or_eq_false_iff.mp hρDD).2
          show numN (true :: ys) ≤ numNBeforeDD (false :: true :: (ys ++ ρ'))
          have hrec : numNBeforeDD (false :: true :: (ys ++ ρ'))
              = numNBeforeDD (true :: (ys ++ ρ')) := rfl
          rw [hrec]
          have := ih hxs
          simpa using this
end Psi
