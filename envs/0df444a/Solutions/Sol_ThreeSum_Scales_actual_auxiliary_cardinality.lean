-- Prove2me | solution 1 for ThreeSum.Scales.actual_auxiliary_cardinality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:33:15.178037+00:00
-- url     : https://prove2.me/submissions/25d789d6-da89-4e3c-82d0-c3cf25c45a7f

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
import Theorems.Thm_ThreeSum_Scales_candidateCount_eventually_gt_multiple
import Theorems.Thm_ThreeSum_Scales_log2_difference_bound

set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, Nat.log2 (3 * n ^ k) < candidateCount n := by
  filter_upwards [candidateCount_eventually_gt_multiple (2 * (k + 2)),
    eventually_ge_atTop (1 : ℕ)] with n hC hn
  exact (log2_difference_bound k (by omega)).trans_lt hC
end ThreeSum.Scales
