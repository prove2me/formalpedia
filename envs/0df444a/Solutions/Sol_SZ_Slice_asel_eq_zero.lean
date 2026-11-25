-- Prove2me | solution 1 for SZ.Slice.asel_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:15:57.873659+00:00
-- url     : https://prove2.me/submissions/1d12dc2f-062d-42b2-a1e5-822b91dcdc8c

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_p_cast_pos

set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
namespace SZ.Slice
theorem _root_.solution {w : ℝ} (h : w - (S.bsel w : ℝ) * S.sq ≤ S.U) : S.asel w = 0 := by
  have hdiv : (w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ) ≤ 0 :=
    (div_le_iff₀ S.p_cast_pos).mpr (by linarith)
  have hc : ⌈(w - (S.bsel w : ℝ) * S.sq - S.U) / (S.p : ℝ)⌉ ≤ 0 :=
    Int.ceil_le.mpr (by push_cast; exact hdiv)
  rw [asel, max_eq_left hc, mul_zero]
end SZ.Slice
