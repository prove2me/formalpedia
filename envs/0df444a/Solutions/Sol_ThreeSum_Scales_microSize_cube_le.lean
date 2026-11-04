-- Prove2me | solution 1 for ThreeSum.Scales.microSize_cube_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:15:12.0672+00:00
-- url     : https://prove2.me/submissions/e708db56-057e-41e0-929b-5f812d03f307

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Sqrt
import Definitions.Def_Submission_ThreeSum_Scales
import Theorems.Thm_ThreeSum_Scales_microSize_rounding

set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
namespace ThreeSum.Scales
theorem _root_.solution (m : ℕ) : microSize m ^ 3 ≤ m := by
  exact (Nat.pow_le_pow_left (microSize_rounding m).1 3).trans
    (Nat.pow_nthRoot_le (Or.inl (by decide : 3 ≠ 0)))
end ThreeSum.Scales
