-- Prove2me | solution 1 for SZ.Slice.bsel_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:25:26.661686+00:00
-- url     : https://prove2.me/submissions/fbb51a50-398e-4dc4-a356-aae7c13a03a2

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_p_pos
import Theorems.Thm_SZ_Slice_p_sq_pos
import Theorems.Thm_SZ_Slice_e_pos

set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
namespace SZ.Slice
theorem _root_.solution {w : ℝ} (hw : 0 ≤ w) : 0 ≤ S.bsel w := by
  have h1 : (0 : ℤ) ≤ ⌊w / ((S.p : ℝ) * S.sq)⌋ :=
    Int.floor_nonneg.mpr (div_nonneg hw S.p_sq_pos.le)
  exact le_min S.e_pos.le (mul_nonneg S.p_pos.le h1)
end SZ.Slice
