-- Prove2me | solution 1 for SZ.Slice.M_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:15:30.810281+00:00
-- url     : https://prove2.me/submissions/99402ef7-975b-47ce-a3dc-b52fe88f57bd

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_m_sub_one_ne

set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
namespace SZ.Slice
theorem _root_.solution : ((S.m : ℝ) - 1) * S.M = (S.e : ℝ) := by
  have h := S.m_sub_one_ne
  rw [M, mul_comm, div_mul_cancel₀ _ h]
end SZ.Slice
