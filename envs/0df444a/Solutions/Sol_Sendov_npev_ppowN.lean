-- Prove2me | solution 1 for Sendov.npev_ppowN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:10:57.103468+00:00
-- url     : https://prove2.me/submissions/6eb93ffa-1a80-459d-a9c0-3219d0ef2da4

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack
import Theorems.Thm_Sendov_npev_nil
import Theorems.Thm_Sendov_npev_cons
import Theorems.Thm_Sendov_unpackN_zero
import Theorems.Thm_Sendov_unpackN_succ
import Theorems.Thm_Sendov_npev_pmulN
attribute [local simp] Sendov.npev_nil
attribute [local simp] Sendov.npev_cons
attribute [local simp] Sendov.unpackN_zero
attribute [local simp] Sendov.unpackN_succ

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (p : List ℕ) (b k : ℕ) : npev (ppowN p k) b = npev p b ^ k := by
  induction k with
  | zero => simp [ppowN]
  | succ k ih => simp only [ppowN, npev_pmulN, ih, pow_succ]; ring
end Sendov
