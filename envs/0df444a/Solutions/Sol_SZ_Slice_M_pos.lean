-- Prove2me | solution 1 for SZ.Slice.M_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:24:48.370047+00:00
-- url     : https://prove2.me/submissions/339e6625-0b1d-4b12-a4b0-b21638fdc4cc

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_e_pos
import Theorems.Thm_SZ_Slice_m_sub_one_pos

set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
namespace SZ.Slice
theorem _root_.solution : 0 < S.M := div_pos (by exact_mod_cast S.e_pos) S.m_sub_one_pos
end SZ.Slice
