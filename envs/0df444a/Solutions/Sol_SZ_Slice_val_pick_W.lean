-- Prove2me | solution 1 for SZ.Slice.val_pick_W
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:04:16.066399+00:00
-- url     : https://prove2.me/submissions/d2e90d04-5f2e-4c91-bc7f-eb6e6fd96bbe

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
theorem _root_.solution (w₀ : ℝ) (k : ℕ) :
    S.val (S.pick (S.W w₀ k)) = (S.dA w₀ k : ℝ) + (S.dB w₀ k : ℝ) * S.sq := rfl
end SZ.Slice
