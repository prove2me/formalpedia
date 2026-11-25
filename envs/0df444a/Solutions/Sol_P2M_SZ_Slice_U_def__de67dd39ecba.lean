-- Prove2me | solution 1 for P2M_SZ_Slice_U_def__de67dd39ecba
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:38:05.985439+00:00
-- url     : https://prove2.me/submissions/f5507d3b-bc1a-457f-a764-af0253997f51

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice

set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
namespace SZ.Slice
theorem _root_.solution : ((S.m : ℝ) - 1) * S.U = (S.e : ℝ) * (1 + S.sq) := S.U_def
end SZ.Slice
