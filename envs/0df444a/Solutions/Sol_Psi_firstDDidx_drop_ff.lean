-- Prove2me | solution 1 for Psi.firstDDidx_drop_ff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:44:07.930439+00:00
-- url     : https://prove2.me/submissions/799f8432-d5cd-49cf-9f28-e515f74f1575

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_firstDDidx_key

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (rest : List Bool) (i : ℕ) (h : firstDDidx rest = some i) :
    ∃ r, rest.drop i = false :: false :: r := by
  induction rest generalizing i with
  | nil => simp [firstDDidx] at h
  | cons a t ih =>
      cases t with
      | nil => rw [show firstDDidx [a] = none from by cases a <;> rfl] at h; simp at h
      | cons b u =>
          rcases firstDDidx_key a b u i h with ⟨rfl, rfl, rfl⟩ | ⟨j, hj, rfl, _⟩
          · exact ⟨u, rfl⟩
          · obtain ⟨r, hr⟩ := ih j hj; exact ⟨r, by rw [List.drop_succ_cons]; exact hr⟩
end Psi
