-- Prove2me | solution 1 for Psi.firstDDidx_prepend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:41:27.052589+00:00
-- url     : https://prove2.me/submissions/05eb78f8-1d82-4369-86b0-c6e08c646f39

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
import Theorems.Thm_Psi_firstDDidx_true
import Theorems.Thm_Psi_firstDDidx_false_headtrue
import Theorems.Thm_Psi_hasDD_cons


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (ρ t : List Bool) (j : ℕ)
    (hρ : hasDD ρ = false) (hhead : t.head? = some true) (ht : firstDDidx t = some j) :
    firstDDidx (ρ ++ t) = some (ρ.length + j) := by
  induction ρ with
  | nil => simpa using ht
  | cons x xs ih =>
      rw [hasDD_cons] at hρ
      have hxsDD : hasDD xs = false := (Bool.or_eq_false_iff.mp hρ).2
      have hihv := ih hxsDD
      cases x with
      | true =>
          rw [List.cons_append, firstDDidx_true, hihv]
          simp only [Option.map_some, List.length_cons]; congr 1; omega
      | false =>
          have h1 := (Bool.or_eq_false_iff.mp hρ).1
          have hLhead : (xs ++ t).head? = some true := by
            cases xs with
            | nil => simpa using hhead
            | cons z zs =>
                simp only [List.head?_cons] at h1
                have : z = true := by
                  by_contra hc; simp only [Bool.not_eq_true] at hc; subst hc; simp at h1
                subst this; simp
          rw [List.cons_append, firstDDidx_false_headtrue _ hLhead, hihv]
          simp only [Option.map_some, List.length_cons]; congr 1; omega
end Psi
