-- Prove2me | solution 1 for ThreeSum.Scales.primeWindow_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:24:32.008942+00:00
-- url     : https://prove2.me/submissions/f278993c-d6d8-4af4-a958-59566303d58e

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
import Theorems.Thm_ThreeSum_Scales_inputBits_tendsto_atTop
import Theorems.Thm_ThreeSum_Scales_natSqrt_tendsto_atTop

set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution : Tendsto primeWindow atTop atTop := by
  have hs := natSqrt_tendsto_atTop.comp inputBits_tendsto_atTop
  apply tendsto_atTop.2
  intro b
  filter_upwards [hs.eventually (eventually_ge_atTop b)] with n hn
  have hp : Nat.sqrt (inputBits n) + 1 < 2 ^ (Nat.sqrt (inputBits n) + 1) :=
    Nat.lt_pow_self (by decide : 1 < 2)
  change b ≤ 2 ^ (Nat.sqrt (inputBits n) + 1)
  exact hn.trans ((Nat.le_succ _).trans hp.le)
end ThreeSum.Scales
