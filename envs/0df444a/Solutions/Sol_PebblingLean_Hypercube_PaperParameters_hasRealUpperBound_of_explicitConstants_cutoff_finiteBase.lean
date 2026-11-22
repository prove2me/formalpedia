-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_explicitConstants_cutoff_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:08:19.212234+00:00
-- url     : https://prove2.me/submissions/fe0936a5-0d9d-4b3e-bc38-147e97d81882

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_Kdom_cutoffAnalyticBudgets_finiteBase

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution
    {n0 : ℕ}
    (hn0_pos : 0 < n0)
    (hn0_growth : 58 ≤ n0)
    (hsplitThreshold : (128 * (217 : ℝ) ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hwidthFitThreshold :
      (128 * ((4 : ℝ) * Real.sqrt 3) ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hcoreNineCutoff :
      81 ≤ (4 : ℝ) ^ 2 * (((3 : ℝ) * (n0 : ℝ) / 4) *
        Real.log (n0 : ℝ)))
    (hwidthConstCutoff :
      Real.log 128 + 4 * Real.log 2 ≤
        ((217 : ℝ) / 30 * Real.log 2) *
          Real.sqrt ((n0 : ℝ) * Real.log (n0 : ℝ)))
    (hstackLogThreshold :
      (32 / stackMargin ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hstackConstCutoff :
      12 * Real.log 2 ≤
        (n0 : ℝ) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound 217 n0) n0) := by
  have hsqrt3_le : Real.sqrt 3 ≤ (2 : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hKdom : 15 * (4 : ℝ) * Real.sqrt 3 ≤ 217 := by
    nlinarith
  have hlog2_lower : (6931471803 : ℝ) / 10000000000 ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hKlarge : 150 ≤ (217 : ℝ) * Real.log 2 := by
    nlinarith
  exact hasRealUpperBound_of_Kdom_cutoffAnalyticBudgets_finiteBase
    (K := (217 : ℝ)) (A := (4 : ℝ)) (n0 := n0)
    hn0_pos
    hn0_growth
    (by norm_num)
    (by norm_num)
    hKdom
    hKlarge
    hsplitThreshold
    (by norm_num)
    hwidthFitThreshold
    hcoreNineCutoff
    hwidthConstCutoff
    hstackLogThreshold
    hstackConstCutoff
end PebblingLean.Hypercube.PaperParameters
