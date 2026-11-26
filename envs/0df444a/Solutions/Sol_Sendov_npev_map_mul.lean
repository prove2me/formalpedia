-- Prove2me | solution 1 for Sendov.npev_map_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:09:03.810925+00:00
-- url     : https://prove2.me/submissions/74195b1c-a78e-4221-811c-2fb961c3df6d

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
theorem _root_.solution (a : ℕ) (q : List ℕ) (b : ℕ) :
    npev (q.map (fun c => a * c)) b = a * npev q b := by
  induction q with
  | nil => simp
  | cons c q ih =>
    simp only [List.map_cons, npev_cons, ih]
    ring
end Sendov
