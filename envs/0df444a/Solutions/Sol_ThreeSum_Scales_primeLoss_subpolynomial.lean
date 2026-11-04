-- Prove2me | solution 1 for ThreeSum.Scales.primeLoss_subpolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:29:18.163858+00:00
-- url     : https://prove2.me/submissions/5a2b4711-3691-44ac-a9c1-7e5fbf112df6

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
import Theorems.Thm_ThreeSum_Scales_eventually_le_rpow_of_log_ratio
import Definitions.Def_WeightedCache3SUM_Alias_7d21bf991a6a3a7b
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (primeLoss radix n : ℝ) ≤ (n : ℝ) ^ d := by
  simpa using eventually_le_rpow_of_log_ratio primeLoss_log_ratio_tendsto_zero hd
end ThreeSum.Scales
