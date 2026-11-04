-- Prove2me | solution 1 for ThreeSum.Scales.primeWindow_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:56:53.828445+00:00
-- url     : https://prove2.me/submissions/2c9fcdca-c18b-43c4-9f9e-be6105655ff5

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
theorem _root_.solution (n : ℕ) : 2 ≤ primeWindow n := by
  unfold primeWindow windowExponent
  rw [pow_succ]
  have hp : 0 < 2 ^ Nat.sqrt (inputBits n) := by positivity
  omega
end ThreeSum.Scales
