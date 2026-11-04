-- Prove2me | solution 1 for ThreeSum.Scales.windowExponent_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:17:09.337755+00:00
-- url     : https://prove2.me/submissions/5731afe7-bd67-4c5d-b19c-dacd3042c048

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
import Theorems.Thm_ThreeSum_Scales_natSqrt_tendsto_atTop

set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution : Tendsto windowExponent atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [natSqrt_tendsto_atTop.eventually (eventually_ge_atTop b)] with m hm
  change b ≤ Nat.sqrt m + 1
  omega
end ThreeSum.Scales
