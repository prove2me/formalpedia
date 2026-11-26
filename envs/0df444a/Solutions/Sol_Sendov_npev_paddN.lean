-- Prove2me | solution 1 for Sendov.npev_paddN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:09:02.015601+00:00
-- url     : https://prove2.me/submissions/64803297-ff13-4374-8211-da9d0ec61df0

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
    npev (paddN p q) b = npev p b + npev q b := by
  induction p generalizing q with
  | nil => simp [paddN]
  | cons a p ih =>
    cases q with
    | nil => simp [paddN]
    | cons c q =>
      simp only [paddN, npev_cons, ih]
      ring
end Sendov
