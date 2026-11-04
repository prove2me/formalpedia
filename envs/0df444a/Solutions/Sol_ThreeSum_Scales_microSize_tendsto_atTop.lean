-- Prove2me | solution 1 for ThreeSum.Scales.microSize_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:09:41.034814+00:00
-- url     : https://prove2.me/submissions/0ffe8f5c-c658-4863-9d3a-9636b448b7d3

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
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution : Tendsto microSize atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop ((b + 2) ^ 3)] with m hm
  have hr : b + 2 ≤ Nat.nthRoot 3 m :=
    (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).mpr hm
  have hround := (microSize_rounding m).2
  omega
end ThreeSum.Scales
