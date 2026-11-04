-- Prove2me | solution 1 for ThreeSum.Scales.cube_lt_microSize_add_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:44:19.8489+00:00
-- url     : https://prove2.me/submissions/f47dbad3-16cd-41bd-a108-5bdf0ff1928d

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
theorem _root_.solution (m : ℕ) : m < (microSize m + 3) ^ 3 := by
  have hroot := Nat.lt_pow_nthRoot_add_one (by decide : 3 ≠ 0) m
  have hround := (microSize_rounding m).2
  exact hroot.trans_le (Nat.pow_le_pow_left (by omega :
    Nat.nthRoot 3 m + 1 ≤ microSize m + 3) 3)
end ThreeSum.Scales
