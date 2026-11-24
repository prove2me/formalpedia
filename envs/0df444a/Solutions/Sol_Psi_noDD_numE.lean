-- Prove2me | solution 1 for Psi.noDD_numE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:31:24.596883+00:00
-- url     : https://prove2.me/submissions/a94dd926-418c-4142-88ef-66a10a322863

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_numE_cons_true
import Theorems.Thm_Psi_numE_cons_false
import Theorems.Thm_Psi_hasDD_cons
import Theorems.Thm_Psi_cV_true_false_head
import Theorems.Thm_Psi_stEast_nonempty


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (hp : hasDD p = false) :
    numE p = numValleys p + (if stEast p false then 1 else 0) := by
  induction p with
  | nil => simp [numE, numValleys, countValleys, stEast]
  | cons a r ih =>
    rw [hasDD_cons] at hp
    simp only [Bool.or_eq_false_iff] at hp
    obtain ⟨hhead, hr⟩ := hp
    cases a with
    | true =>
      rw [numE_cons_true]
      have hv : numValleys (true :: r) = numValleys r := by simp [numValleys, countValleys]
      have hs : stEast (true :: r) false = stEast r false := rfl
      rw [hv, hs]; exact ih hr
    | false =>
      rw [numE_cons_false]
      have hnf : r.head? ≠ some false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne] at hhead
        rcases hhead with h | h
        · simp at h
        · exact h
      have hv : numValleys (false :: r) = countValleys r true := by simp [numValleys, countValleys]
      have hs : stEast (false :: r) false = stEast r true := rfl
      rw [hv, hs]
      cases r with
      | nil => simp [numE, countValleys, stEast]
      | cons b r'' =>
        have hb : b = true := by cases b with | true => rfl | false => exact absurd rfl hnf
        subst hb
        rw [cV_true_false_head (true :: r'') rfl,
            stEast_nonempty (true :: r'') (by simp) true false]
        have := ih hr
        simp only [numValleys] at this ⊢
        omega
end Psi
