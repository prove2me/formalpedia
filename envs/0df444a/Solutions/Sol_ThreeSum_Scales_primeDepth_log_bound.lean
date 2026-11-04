-- Prove2me | solution 1 for ThreeSum.Scales.primeDepth_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:17:08.248518+00:00
-- url     : https://prove2.me/submissions/3a58bcc1-b70b-4fc6-8166-f6196912ecb9

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
import Theorems.Thm_ThreeSum_Scales_primeWindow_ge_two
import Theorems.Thm_ThreeSum_Scales_primeDepth_upper
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
theorem _root_.solution {n : ℕ} (hR : 4 ≤ radix n) :
    (primeDepth radix n : ℝ) * Real.log (4 * primeWindow n : ℝ) ≤
      Real.log (radix n : ℝ) := by
  have hp := primeDepth_upper radix hR
  have hpow : (4 * primeWindow n) ^ primeDepth radix n ≤ radix n := by omega
  have hpos : (0 : ℝ) < ((4 * primeWindow n : ℕ) : ℝ) ^ primeDepth radix n := by
    have hy := primeWindow_ge_two n
    positivity
  have hpowR : ((4 * primeWindow n : ℕ) : ℝ) ^ primeDepth radix n ≤ (radix n : ℝ) := by
    exact_mod_cast hpow
  have hl := Real.log_le_log hpos hpowR
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Real.log_pow] using hl
end ThreeSum.Scales
