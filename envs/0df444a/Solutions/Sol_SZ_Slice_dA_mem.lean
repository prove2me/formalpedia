-- Prove2me | solution 1 for SZ.Slice.dA_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:30:47.55032+00:00
-- url     : https://prove2.me/submissions/85c91102-fa26-4465-8904-ef2b15073769

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_pick_adm
import Theorems.Thm_SZ_Slice_W_mem

set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
variable {S}
namespace SZ.Slice
theorem _root_.solution {w₀ : ℝ} (h0 : 0 ≤ w₀) (h1 : w₀ ≤ (S.m : ℝ) * S.U) (k : ℕ) :
    S.PDigit (S.dA w₀ k) :=
  ((S.pick_adm (W_mem h0 h1 k).1 (W_mem h0 h1 k).2).1)
end SZ.Slice
