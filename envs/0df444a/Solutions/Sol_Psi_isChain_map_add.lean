-- Prove2me | solution 1 for Psi.isChain_map_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:48:06.137484+00:00
-- url     : https://prove2.me/submissions/cacc5714-6180-493e-804a-d9c702933405

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (l : List ℕ) (c : ℕ) (h : l.IsChain (· ≤ ·)) :
    (l.map (· + c)).IsChain (· ≤ ·) := by
  induction l with
  | nil => simp
  | cons x xs ih => cases xs with
    | nil => simp
    | cons y ys =>
      rw [List.isChain_cons_cons] at h
      simp only [List.map_cons]
      rw [List.isChain_cons_cons]
      exact ⟨by omega, by have := ih h.2; simpa using this⟩
end Psi
