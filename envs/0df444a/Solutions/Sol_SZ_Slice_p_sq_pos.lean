-- Prove2me | solution 1 for SZ.Slice.p_sq_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:19:40.273744+00:00
-- url     : https://prove2.me/submissions/26e3294c-4e11-4aa1-b023-736aea36c7d8

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_sq_pos
import Theorems.Thm_SZ_Slice_p_cast_pos

set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
namespace SZ.Slice
theorem _root_.solution : (0 : ℝ) < (S.p : ℝ) * S.sq := mul_pos S.p_cast_pos S.sq_pos
end SZ.Slice
