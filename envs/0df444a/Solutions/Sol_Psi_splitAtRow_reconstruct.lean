-- Prove2me | solution 1 for Psi.splitAtRow_reconstruct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:43:55.700929+00:00
-- url     : https://prove2.me/submissions/9a515bfd-f944-4767-bbec-feb807bf1483

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
import Theorems.Thm_Psi_allfalse_noDD
import Theorems.Thm_Psi_hasDD_cons
import Theorems.Thm_Psi_numN_cons_false
import Theorems.Thm_Psi_numN_cons_true


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (ρ ρ' : List Bool)
    (hne0 : numN ρ = 0 → ρ = []) (hρDD : hasDD ρ = false)
    (hmax : ρ.getLast? ≠ some true ∨ ρ'.head? ≠ some false) :
    splitAtRow (ρ ++ ρ') (numN ρ) = (ρ, ρ') := by
  induction ρ with
  | nil => simp [numN, splitAtRow]
  | cons x xs ih =>
      have hxsDD : hasDD xs = false := by
        have h := hρDD; rw [hasDD_cons] at h; exact (Bool.or_eq_false_iff.mp h).2
      cases x with
      | false =>
          rw [numN_cons_false]
          have hxsne : numN xs ≠ 0 := fun h0 => by
            have := hne0 (by rw [numN_cons_false]; exact h0); simp at this
          have hxsnil : xs ≠ [] := fun h => by rw [h] at hxsne; simp [numN] at hxsne
          obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hxsnil
          obtain ⟨m, hm⟩ : ∃ m, numN (y :: ys) = m + 1 := ⟨numN (y :: ys) - 1, by omega⟩
          rw [hm]
          show splitAtRow (false :: (y :: ys ++ ρ')) (m + 1) = _
          have hmaxxs : (y :: ys).getLast? ≠ some true ∨ ρ'.head? ≠ some false := by
            rcases hmax with hm2 | hm2
            · left; rwa [List.getLast?_cons_cons] at hm2
            · right; exact hm2
          have hih := ih (fun h => by rw [h] at hm; simp at hm) hxsDD hmaxxs
          rw [hm] at hih; rw [splitAtRow, hih]
      | true =>
          rw [numN_cons_true]
          rcases Nat.eq_zero_or_pos (numN xs) with h0 | hpos
          · rw [h0]
            rcases allfalse_noDD xs h0 hxsDD with rfl | rfl
            · have hh : ρ'.head? ≠ some false := Or.resolve_left hmax (by simp)
              show splitAtRow (true :: ρ') 1 = ([true], ρ')
              cases ρ' with
              | nil => simp [splitAtRow]
              | cons z zs =>
                  simp only [List.head?_cons, ne_eq, Option.some.injEq] at hh
                  have : z = true := by cases z with | false => simp at hh | true => rfl
                  subst this; simp [splitAtRow]
            · show splitAtRow (true :: false :: ρ') 1 = ([true, false], ρ')
              simp [splitAtRow]
          · obtain ⟨m, hm⟩ : ∃ m, numN xs = m + 1 := ⟨numN xs - 1, by omega⟩
            rw [hm]
            have hxsnil : xs ≠ [] := fun h => by rw [h] at hm; simp [numN] at hm
            obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hxsnil
            show splitAtRow (true :: (y :: ys ++ ρ')) (m + 1 + 1) = _
            have hmaxxs : (y :: ys).getLast? ≠ some true ∨ ρ'.head? ≠ some false := by
              rcases hmax with hm2 | hm2
              · left; rwa [List.getLast?_cons_cons] at hm2
              · right; exact hm2
            have hih := ih (fun h => by rw [h] at hm; simp at hm) hxsDD hmaxxs
            rw [hm] at hih; rw [splitAtRow, hih]
end Psi
