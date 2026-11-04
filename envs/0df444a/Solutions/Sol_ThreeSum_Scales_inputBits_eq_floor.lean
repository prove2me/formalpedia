-- Prove2me | solution 1 for ThreeSum.Scales.inputBits_eq_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:16:23.647201+00:00
-- url     : https://prove2.me/submissions/44df15d9-0cba-4283-8891-49278709fe59

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
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution (n : ℕ) : inputBits n = ⌊Real.logb 2 (n : ℝ)⌋₊ := by
  rw [inputBits, Nat.log2_eq_log_two]
  exact (Real.natFloor_logb_natCast 2 n).symm
end ThreeSum.Scales
