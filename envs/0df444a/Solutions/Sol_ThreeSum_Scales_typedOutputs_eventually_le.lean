-- Prove2me | solution 1 for ThreeSum.Scales.typedOutputs_eventually_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:33:10.015406+00:00
-- url     : https://prove2.me/submissions/29dddcf7-e642-4b91-bc19-4755c779819f

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
import Definitions.Def_WeightedCache3SUM_Alias_e8286cd6503d6aa9
import Theorems.Thm_ThreeSum_Scales_eventually_le_rpow_of_log_ratio

set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (typedOutputs n : ℝ) ≤ (n : ℝ) ^ (2 * Parameters.E / 5 + d) :=
  eventually_le_rpow_of_log_ratio typedOutputs_log_ratio_tendsto hd
end ThreeSum.Scales
