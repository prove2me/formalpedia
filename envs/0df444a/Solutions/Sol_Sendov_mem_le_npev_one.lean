-- Prove2me | solution 1 for Sendov.mem_le_npev_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:09:27.583807+00:00
-- url     : https://prove2.me/submissions/af8c4bf2-b80c-46a8-9735-c5d97419a474

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack
import Theorems.Thm_Sendov_npev_nil
import Theorems.Thm_Sendov_npev_cons
import Theorems.Thm_Sendov_unpackN_zero
import Theorems.Thm_Sendov_unpackN_succ
attribute [local simp] Sendov.npev_nil
attribute [local simp] Sendov.npev_cons
attribute [local simp] Sendov.unpackN_zero
attribute [local simp] Sendov.unpackN_succ

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution : ∀ (q : List ℕ) (a : ℕ), a ∈ q → a ≤ npev q 1 := by
  intro q
  induction q with
  | nil => intro a ha; cases ha
  | cons c q ih =>
    intro a ha
    rcases List.mem_cons.1 ha with h | h
    · subst h; simp
    · have := ih a h
      simp only [npev_cons, one_mul]
      omega
end Sendov
