-- Prove2me | solution 1 for SZ.Slice.dB_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:29:55.169029+00:00
-- url     : https://prove2.me/submissions/3049adbe-b467-44cb-8363-fee5a45aa460

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
    S.PDigit (S.dB w₀ k) :=
  ((S.pick_adm (W_mem h0 h1 k).1 (W_mem h0 h1 k).2).2.1)
end SZ.Slice
