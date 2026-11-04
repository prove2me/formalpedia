-- Prove2me | solution 1 for ThreeSum.Scales.radix_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:58:19.090612+00:00
-- url     : https://prove2.me/submissions/a3f23e58-46a5-45aa-a194-c61738c1c9a6

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
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_pos


set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution (n : ℕ) : 0 < radix n := by
  unfold radix localRadix
  exact Nat.pow_pos (LocalCoverBounds.localPrime_pos _)
end ThreeSum.Scales
