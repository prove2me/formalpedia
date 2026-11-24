-- Prove2me | solution 1 for Psi.firstDDidx_prev_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:44:29.813718+00:00
-- url     : https://prove2.me/submissions/982801ea-1ff0-429d-bc84-48d2457218cd

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_firstDDidx_key

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (rest : List Bool) (i : ℕ) (h : firstDDidx rest = some i) (hi : 1 ≤ i) :
    (rest.take i).getLast? = some true := by
  induction rest generalizing i with
  | nil => simp [firstDDidx] at h
  | cons a t ih =>
      cases t with
      | nil => rw [show firstDDidx [a] = none from by cases a <;> rfl] at h; simp at h
      | cons b u =>
          rcases firstDDidx_key a b u i h with ⟨rfl, rfl, rfl⟩ | ⟨j, hj, rfl, hne⟩
          · omega
          · rw [List.take_succ_cons]
            cases j with
            | zero =>
                have hbf : b = false := by
                  rcases firstDDidx_key b (u.headD false) (u.tail) 0 (by
                    cases u with
                    | nil => simp [firstDDidx] at hj
                    | cons c v => simpa using hj) with ⟨hb, _, _⟩ | ⟨_, _, hc, _⟩
                  · exact hb
                  · omega
                have haf : a = true := by
                  by_contra hc; simp only [Bool.not_eq_true] at hc; exact hne ⟨hc, hbf⟩
                subst haf; simp
            | succ n =>
                rw [List.take_succ_cons, List.getLast?_cons_cons]
                have := ih (n + 1) hj (by omega)
                rw [List.take_succ_cons] at this
                exact this
end Psi
