-- Prove2me | solution 1 for ThreeSum.Scales.microSize_rounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:05:46.692715+00:00
-- url     : https://prove2.me/submissions/f8de80f3-064a-4372-b996-eae3b766b38b

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

set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
namespace ThreeSum.Scales
theorem _root_.solution (m : ℕ) :
    microSize m ≤ Nat.nthRoot 3 m ∧ Nat.nthRoot 3 m < microSize m + 2 := by
  have h := Nat.mod_add_div (Nat.nthRoot 3 m) 2
  have hr := Nat.mod_lt (Nat.nthRoot 3 m) (by decide : 0 < 2)
  unfold microSize
  omega
end ThreeSum.Scales
