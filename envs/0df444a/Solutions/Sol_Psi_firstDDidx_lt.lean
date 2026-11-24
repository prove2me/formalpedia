-- Prove2me | solution 1 for Psi.firstDDidx_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:43:18.173799+00:00
-- url     : https://prove2.me/submissions/1928a287-d17f-4d49-8dda-775d4dba116f

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_firstDDidx_key

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (rest : List Bool) (i : ℕ) (h : firstDDidx rest = some i) :
    i + 1 < rest.length := by
  induction rest generalizing i with
  | nil => simp [firstDDidx] at h
  | cons a t ih =>
      cases t with
      | nil => rw [show firstDDidx [a] = none from by cases a <;> rfl] at h; simp at h
      | cons b u =>
          rcases firstDDidx_key a b u i h with ⟨rfl, rfl, rfl⟩ | ⟨j, hj, rfl, _⟩
          · simp
          · have := ih j hj; simp only [List.length_cons] at this ⊢; omega
end Psi
