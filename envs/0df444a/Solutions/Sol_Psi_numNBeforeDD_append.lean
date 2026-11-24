-- Prove2me | solution 1 for Psi.numNBeforeDD_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:18:42.975626+00:00
-- url     : https://prove2.me/submissions/a7461ff8-6246-41e9-b5bb-9e1d5524bf2d

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection
import Theorems.Thm_Psi_numNBeforeDD_cons_true
import Theorems.Thm_Psi_hasDD_cons
import Theorems.Thm_Psi_numN_cons_false
import Theorems.Thm_Psi_numN_cons_true


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (s t : List Bool) (hs : hasDD s = false)
    (hbnd : ¬ (s.getLast? = some false ∧ t.head? = some false)) :
    numNBeforeDD (s ++ t) = numN s + numNBeforeDD t := by
  induction s with
  | nil => simp [numN]
  | cons x xs ih =>
    cases x with
    | true =>
      have hxs : hasDD xs = false := by rw [hasDD_cons] at hs; exact (Bool.or_eq_false_iff.mp hs).2
      have hbnd' : ¬ (xs.getLast? = some false ∧ t.head? = some false) := by
        cases xs with
        | nil => rintro ⟨h1, _⟩; simp at h1
        | cons z zs => rw [List.getLast?_cons_cons] at hbnd; exact hbnd
      simp only [List.cons_append, numNBeforeDD_cons_true, numN_cons_true]
      rw [ih hxs hbnd']; omega
    | false =>
      have hxs : hasDD xs = false := by rw [hasDD_cons] at hs; exact (Bool.or_eq_false_iff.mp hs).2
      rw [numN_cons_false, List.cons_append]
      cases xs with
      | nil =>
        have ht : t.head? ≠ some false := by intro hc; exact hbnd ⟨by simp, hc⟩
        cases t with
        | nil => simp [numNBeforeDD, numN]
        | cons z zs =>
          have hz : z = true := by cases z with | true => rfl | false => simp at ht
          subst hz; simp [numNBeforeDD, numN]
      | cons y ys =>
        have hy : y = true := by cases y with | true => rfl | false => simp [hasDD] at hs
        subst hy
        have hbnd' : ¬ ((true :: ys).getLast? = some false ∧ t.head? = some false) := by
          rw [List.getLast?_cons_cons] at hbnd; exact hbnd
        show numNBeforeDD (false :: true :: (ys ++ t)) = numN (true :: ys) + numNBeforeDD t
        have hrec : numNBeforeDD (false :: true :: (ys ++ t))
            = numNBeforeDD (true :: (ys ++ t)) := rfl
        rw [hrec]
        have := ih hxs hbnd'
        simpa using this
end Psi
