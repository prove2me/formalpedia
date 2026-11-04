-- Prove2me | solution 1 for ThreeSum.Scales.totalSize_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:44:33.101062+00:00
-- url     : https://prove2.me/submissions/931c3e47-1e07-4def-baad-29a835ecb575

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
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
namespace ThreeSum.Scales
theorem _root_.solution {m : ℕ} (hm : 0 < microSize m) :
    m < 5 * totalSize m + 100 * microSize m := by
  have hmod := Nat.mod_lt m (by omega : 0 < 100 * microSize m)
  have hdiv := Nat.mod_add_div m (100 * microSize m)
  have heq : 5 * totalSize m = 100 * microSize m * (m / (100 * microSize m)) := by
    simp only [totalSize, blockCount]
    ring
  omega
end ThreeSum.Scales
