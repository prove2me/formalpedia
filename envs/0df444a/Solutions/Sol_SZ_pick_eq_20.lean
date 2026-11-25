-- Prove2me | solution 1 for SZ.pick_eq_20
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:53:07.036495+00:00
-- url     : https://prove2.me/submissions/7a95621d-04ef-4b32-bc51-3d86882ddf58

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {w : ℝ} (h1 : 1 + Real.sqrt 3 < w) (h2 : w < 2 * Real.sqrt 3) :
    pick w = (2, 0) := by
  unfold pick; rw [if_neg (not_le.mpr h1), if_pos h2]
end SZ
