-- Prove2me | solution 1 for Psi.firstDDidx_take_noDD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:44:19.838835+00:00
-- url     : https://prove2.me/submissions/9ceb846a-cf70-4ee8-9166-6e24019de92e

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_firstDDidx_key
import Theorems.Thm_Psi_hasDD_cons


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (rest : List Bool) (i : ℕ) (h : firstDDidx rest = some i) :
    hasDD (rest.take i) = false := by
  induction rest generalizing i with
  | nil => simp [firstDDidx] at h
  | cons a t ih =>
      cases t with
      | nil => rw [show firstDDidx [a] = none from by cases a <;> rfl] at h; simp at h
      | cons b u =>
          rcases firstDDidx_key a b u i h with ⟨rfl, rfl, rfl⟩ | ⟨j, hj, rfl, hne⟩
          · rfl
          · rw [List.take_succ_cons, hasDD_cons]
            have ihv := ih j hj
            cases j with
            | zero => simp [hasDD]
            | succ n =>
                rw [List.take_succ_cons] at ihv ⊢
                rw [List.head?_cons]
                have hand : (a == false && some b == some false) = false := by
                  by_cases ha : a = false <;> by_cases hb : b = false <;> simp_all
                rw [hand, Bool.false_or]; exact ihv
end Psi
