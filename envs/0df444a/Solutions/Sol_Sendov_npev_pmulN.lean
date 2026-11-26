-- Prove2me | solution 1 for Sendov.npev_pmulN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:09:49.880477+00:00
-- url     : https://prove2.me/submissions/d9716b36-23ff-4039-a904-81b1dfcc862c

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Sendov_FiniteRange_Pack
import Theorems.Thm_Sendov_npev_nil
import Theorems.Thm_Sendov_npev_cons
import Theorems.Thm_Sendov_unpackN_zero
import Theorems.Thm_Sendov_unpackN_succ
import Theorems.Thm_Sendov_npev_paddN
import Theorems.Thm_Sendov_npev_map_mul
attribute [local simp] Sendov.npev_nil
attribute [local simp] Sendov.npev_cons
attribute [local simp] Sendov.unpackN_zero
attribute [local simp] Sendov.unpackN_succ

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (p q : List ℕ) (b : ℕ) :
    npev (pmulN p q) b = npev p b * npev q b := by
  induction p with
  | nil => simp [pmulN]
  | cons a p ih =>
    simp only [pmulN, npev_paddN, npev_map_mul, npev_cons, ih]
    ring
end Sendov
