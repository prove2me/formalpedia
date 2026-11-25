-- Prove2me | solution 1 for SZ.Slice.isDigits_dB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:33:14.207271+00:00
-- url     : https://prove2.me/submissions/6e26554c-21e0-46ef-a416-853bf3b14564

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_dB_mem

set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
variable {S}
namespace SZ.Slice
theorem _root_.solution {w₀ : ℝ} (h0 : 0 ≤ w₀) (h1 : w₀ ≤ (S.m : ℝ) * S.U) :
    IsDigits S.m (S.dB w₀) :=
  { two_le := by have := S.three_le; omega
    nonneg := fun i => (dB_mem h0 h1 i).2.1
    le_sub_one := fun i => le_trans (dB_mem h0 h1 i).2.2 S.e_le }
end SZ.Slice
