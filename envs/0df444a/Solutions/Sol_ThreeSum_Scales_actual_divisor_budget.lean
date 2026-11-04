-- Prove2me | solution 1 for ThreeSum.Scales.actual_divisor_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:00:47.446124+00:00
-- url     : https://prove2.me/submissions/83a1bc68-1783-42c0-a574-428ff4ef629c

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
import Theorems.Thm_ThreeSum_Scales_actual_candidate_density
import Theorems.Thm_ThreeSum_Scales_log_difference_bound
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
theorem _root_.solution (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      divisorBudget k n * primeWindow n ≤
        (PrimeDensity.candidates (primeWindow n)).card * (4 * (k + 2) * (inputBits n + 1)) := by
  filter_upwards [actual_candidate_density, eventually_ge_atTop (1 : ℕ)] with n hC hn
  have hy := primeWindow_ge_two n
  have hlog : 0 < Real.log (primeWindow n : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < primeWindow n))
  have hK : (divisorBudget k n : ℝ) ≤
      Real.log (3 * n ^ k : ℝ) / Real.log (primeWindow n : ℝ) := by
    simpa [divisorBudget, Real.logb] using
      Real.natLog_le_logb (3 * n ^ k) (primeWindow n)
  have hKmul := (le_div_iff₀ hlog).mp hK
  have hCmul := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * Real.log (primeWindow n : ℝ))).mp hC
  have hdiff := log_difference_bound k (by omega : 0 < n)
  have hr : (divisorBudget k n : ℝ) * primeWindow n ≤
      ((PrimeDensity.candidates (primeWindow n)).card : ℝ) *
        (4 * ((k : ℝ) + 2) * (inputBits n + 1)) := by
    calc
      (divisorBudget k n : ℝ) * primeWindow n ≤
          (divisorBudget k n : ℝ) *
            (((PrimeDensity.candidates (primeWindow n)).card : ℝ) *
              (4 * Real.log (primeWindow n : ℝ))) :=
        mul_le_mul_of_nonneg_left hCmul (Nat.cast_nonneg _)
      _ = (4 * (PrimeDensity.candidates (primeWindow n)).card : ℝ) *
          ((divisorBudget k n : ℝ) * Real.log (primeWindow n : ℝ)) := by ring
      _ ≤ (4 * (PrimeDensity.candidates (primeWindow n)).card : ℝ) *
          Real.log (3 * n ^ k : ℝ) := mul_le_mul_of_nonneg_left hKmul (by positivity)
      _ ≤ (4 * (PrimeDensity.candidates (primeWindow n)).card : ℝ) *
          (((k : ℝ) + 2) * (inputBits n + 1)) := mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = _ := by ring
  exact_mod_cast hr
end ThreeSum.Scales
