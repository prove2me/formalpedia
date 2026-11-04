-- Prove2me | solution 1 for ThreeSum.Scales.localThreshold_log_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:44:38.896532+00:00
-- url     : https://prove2.me/submissions/19e40f16-c043-4371-aef5-a297230ed602

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
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution (h : ℕ) :
    Real.log (LocalCoverBounds.localThreshold h : ℝ) =
      Real.log (LocalCoverBounds.outputCount (512 * h) h : ℝ) +
        (2 * h : ℝ) * Real.log 2 := by
  have hM : (0 : ℝ) < LocalCoverBounds.outputCount (512 * h) h := by
    exact_mod_cast (Nat.choose_pos (by omega : 2 * h ≤ 512 * h))
  simp only [LocalCoverBounds.localThreshold, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_mul (ne_of_gt hM) (by positivity), Real.log_pow]
  simp
end ThreeSum.Scales
