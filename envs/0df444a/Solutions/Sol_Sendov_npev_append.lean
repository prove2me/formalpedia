-- Prove2me | solution 1 for Sendov.npev_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:07:57.71088+00:00
-- url     : https://prove2.me/submissions/c766754d-33cc-41d3-beec-c148803f6580

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
theorem _root_.solution (p q : List ℕ) (b : ℕ) :
    npev (p ++ q) b = npev p b + b ^ p.length * npev q b := by
  induction p with
  | nil => simp
  | cons a p ih =>
    simp only [List.cons_append, npev_cons, ih, List.length_cons]
    ring
end Sendov
