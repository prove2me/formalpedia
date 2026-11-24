-- Prove2me | solution 1 for Psi.isChain_map_add_reflect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:34:34.146366+00:00
-- url     : https://prove2.me/submissions/56c468cf-02b4-4095-958f-50898df1165f

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (l : List ℕ) (c : ℕ)
    (h : (l.map (· + c)).IsChain (· ≤ ·)) : l.IsChain (· ≤ ·) := by
  induction l with
  | nil => simp
  | cons x xs ih => cases xs with
    | nil => simp
    | cons y ys =>
      simp only [List.map_cons] at h
      rw [List.isChain_cons_cons] at h ⊢
      exact ⟨by omega, ih (by simpa using h.2)⟩
end Psi
