-- Prove2me | solution 1 for Psi.firstDDidx_key
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:04:09.669818+00:00
-- url     : https://prove2.me/submissions/e46a48cb-39a9-42ab-8596-43f7efb76f52

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse
import Theorems.Thm_Psi_firstDDidx_ff
import Theorems.Thm_Psi_firstDDidx_ft
import Theorems.Thm_Psi_firstDDidx_true


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a b : Bool) (u : List Bool) (i : ℕ)
    (h : firstDDidx (a :: b :: u) = some i) :
    (a = false ∧ b = false ∧ i = 0) ∨
      (∃ j, firstDDidx (b :: u) = some j ∧ i = j + 1 ∧ ¬(a = false ∧ b = false)) := by
  cases a with
  | true =>
      right; rw [firstDDidx_true] at h
      obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨j, hj, rfl, by simp⟩
  | false => cases b with
    | false => left; rw [firstDDidx_ff] at h; exact ⟨rfl, rfl, (Option.some.inj h).symm⟩
    | true =>
        right; rw [firstDDidx_ft] at h
        obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
        exact ⟨j, hj, rfl, by simp⟩
end Psi
