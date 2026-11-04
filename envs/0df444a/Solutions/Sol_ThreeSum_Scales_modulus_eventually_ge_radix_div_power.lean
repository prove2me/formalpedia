-- Prove2me | solution 1 for ThreeSum.Scales.modulus_eventually_ge_radix_div_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:33:12.533083+00:00
-- url     : https://prove2.me/submissions/3f32dacf-f35b-4d5e-a059-f400883152f1

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
import Definitions.Def_WeightedCache3SUM_Alias_9e4cafb1427c81bb
import Theorems.Thm_ThreeSum_Scales_primeLoss_subpolynomial
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
theorem _root_.solution {P : ℕ → ℕ}
    (hP : ∀ᶠ n : ℕ in atTop, primeWindow n ^ primeDepth radix n ≤ P n)
    {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (radix n : ℝ) / (n : ℝ) ^ d ≤ P n := by
  filter_upwards [hP, primeLoss_subpolynomial hd, eventually_ge_atTop (1 : ℕ)] with n hP hn hnpos
  have hbound : (radix n : ℝ) ≤ (primeLoss radix n : ℝ) * P n := by
    exact_mod_cast primeDepth_loss_bound radix hP
  have hbound' : (radix n : ℝ) ≤ (n : ℝ) ^ d * P n :=
    hbound.trans (mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg _))
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ d)).mpr
  simpa only [mul_comm] using hbound'
end ThreeSum.Scales
