-- Prove2me | solution 1 for ThreeSum.Scales.microHalf_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:13:21.569589+00:00
-- url     : https://prove2.me/submissions/1dcd74b3-03d5-44f2-82e8-b196cdf37042

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
import Theorems.Thm_ThreeSum_Scales_microSize_tendsto_atTop

set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution : Tendsto microHalf atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [microSize_tendsto_atTop.eventually (eventually_ge_atTop (2 * b))] with m hm
  change 2 * microHalf m ≥ 2 * b at hm
  omega
end ThreeSum.Scales
