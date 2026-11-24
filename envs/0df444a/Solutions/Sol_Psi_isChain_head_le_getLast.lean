-- Prove2me | solution 1 for Psi.isChain_head_le_getLast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:34:29.46635+00:00
-- url     : https://prove2.me/submissions/40829694-1d64-4def-9aa8-7e9c1695314d

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (l : List ℕ) (hc : l.IsChain (· ≤ ·)) (g : ℕ)
    (hg : l.getLast? = some g) : l.headD 0 ≤ g := by
  induction l with
  | nil => simp at hg
  | cons x xs ih =>
    cases xs with
    | nil => simp only [List.getLast?_singleton, Option.some.injEq] at hg; subst hg; simp
    | cons y ys =>
      rw [List.isChain_cons_cons] at hc
      have hg' : (y :: ys).getLast? = some g := by rw [← hg]; simp [List.getLast?_cons_cons]
      have := ih hc.2 hg'
      simp only [List.headD_cons] at this ⊢
      omega
end Psi
