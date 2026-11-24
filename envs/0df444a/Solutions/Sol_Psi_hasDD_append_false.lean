-- Prove2me | solution 1 for Psi.hasDD_append_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:59:03.276288+00:00
-- url     : https://prove2.me/submissions/8fd70423-08a2-46c3-a45e-17e949ad83a6

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_hasDD_cons
import Theorems.Thm_Psi_stEast_nonempty


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (s t : List Bool) (hs : hasDD s = false) (ht : hasDD t = false)
    (hbound : stEast s false = true → t.head? ≠ some false) : hasDD (s ++ t) = false := by
  induction s with
  | nil => simpa using ht
  | cons a s' ih =>
    rw [hasDD_cons a s'] at hs
    simp only [Bool.or_eq_false_iff] at hs
    obtain ⟨hhd, hs'⟩ := hs
    rw [List.cons_append, hasDD_cons a (s' ++ t)]
    simp only [Bool.or_eq_false_iff]
    refine ⟨?_, ?_⟩
    · cases s' with
      | nil =>
        simp only [List.nil_append]
        cases hb : (a == false && t.head? == some false) with
        | false => rfl
        | true =>
          exfalso
          simp only [Bool.and_eq_true, beq_iff_eq] at hb
          obtain ⟨ha, hth⟩ := hb
          have hse : stEast [a] false = true := by cases a <;> simp_all [stEast]
          exact hbound hse hth
      | cons y ys => simpa using hhd
    · apply ih hs'
      intro hse
      cases s' with
      | nil => simp [stEast] at hse
      | cons y ys =>
        have hst : stEast (a :: y :: ys) false = stEast (y :: ys) false := by
          cases a <;> (simp only [stEast] <;> exact stEast_nonempty (y::ys) (by simp) _ _)
        rw [hst] at hbound; exact hbound hse
end Psi
