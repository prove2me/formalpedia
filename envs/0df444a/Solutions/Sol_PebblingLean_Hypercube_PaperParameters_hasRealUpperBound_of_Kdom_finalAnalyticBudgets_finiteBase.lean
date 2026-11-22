-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_Kdom_finalAnalyticBudgets_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:06:28.328069+00:00
-- url     : https://prove2.me/submissions/245ae015-53c9-472c-969b-056c796f4615

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_three_quarters_le_splitA_of_four_mul_le
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_three_annulusWidthCore_add_one_le_splitA_of_coarse
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidthCore_ge_nine_of_coarse_sq
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_chernoff_core_sq_of_A_sq_ge
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulus_core_nine_budget_of_cutoff
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_Kdom_deterministicCutoffs_chernoffCoreWidth_finiteBase
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_four_mul_splitM_le_of_Knonneg_splitThreshold

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution
    {K A : ℝ} {n0 : ℕ}
    (hn0_pos : 0 < n0)
    (hn0_growth : 58 ≤ n0)
    (hK : 0 ≤ K)
    (hA : 0 ≤ A)
    (hKdom : 15 * A * Real.sqrt 3 ≤ K)
    (hKlarge : 150 ≤ K * Real.log 2)
    (hsplitThreshold : (128 * K ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hA_sq : 16 ≤ A ^ 2)
    (hthreeCoreCoarse :
      ∀ n : ℕ, n0 ≤ n →
        3 * (A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1) ≤
          (3 : ℝ) * (n : ℝ) / 4)
    (hcoreNineCutoff :
      81 ≤ A ^ 2 * (((3 : ℝ) * (n0 : ℝ) / 4) *
        Real.log (n0 : ℝ)))
    (hwidthConstCutoff :
      Real.log 128 + 4 * Real.log 2 ≤
        (K / 30 * Real.log 2) *
          Real.sqrt ((n0 : ℝ) * Real.log (n0 : ℝ)))
    (hstackLogThreshold :
      (32 / stackMargin ^ 2) ^ 2 ≤ (n0 : ℝ))
    (hstackConstCutoff :
      12 * Real.log 2 ≤
        (n0 : ℝ) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) :=
  hasRealUpperBound_of_Kdom_deterministicCutoffs_chernoffCoreWidth_finiteBase
    (K := K) (A := A) (n0 := n0)
    hn0_pos
    hn0_growth
    hK
    hA
    hKdom
    hKlarge
    hsplitThreshold
    (fun n hn => by
      have hquarter :=
        four_mul_splitM_le_of_Knonneg_splitThreshold
          (K := K) (n0 := n0) (n := n)
          hK hn0_growth hsplitThreshold hn
      exact three_annulusWidthCore_add_one_le_splitA_of_coarse
        (A := A) (K := K) (n := n)
        hA
        (by omega : 2 ≤ n)
        (three_quarters_le_splitA_of_four_mul_le hquarter)
        (hthreeCoreCoarse n hn))
    (fun n hn => by
      have hquarter :=
        four_mul_splitM_le_of_Knonneg_splitThreshold
          (K := K) (n0 := n0) (n := n)
          hK hn0_growth hsplitThreshold hn
      exact annulusWidthCore_ge_nine_of_coarse_sq
        (A := A) (K := K) (n := n)
        hA
        (by omega : 1 ≤ n)
        (three_quarters_le_splitA_of_four_mul_le hquarter)
        (annulus_core_nine_budget_of_cutoff
          (A := A) (n0 := n0) (n := n)
          (by omega : 1 ≤ n0)
          hn
          hcoreNineCutoff))
    (fun n hn => by
      have hquarter :=
        four_mul_splitM_le_of_Knonneg_splitThreshold
          (K := K) (n0 := n0) (n := n)
          hK hn0_growth hsplitThreshold hn
      have ha_lower :=
        three_quarters_le_splitA_of_four_mul_le
          (K := K) (n := n) hquarter
      have hnreal : (58 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (hn0_growth.trans hn)
      have ha_three : 3 ≤ (splitA K n : ℝ) := by
        nlinarith
      exact chernoff_core_sq_of_A_sq_ge
        (A := A) (K := K) (n := n)
        (by omega : 1 ≤ n)
        ha_three
        hA_sq)
    hwidthConstCutoff
    hstackLogThreshold
    hstackConstCutoff
end PebblingLean.Hypercube.PaperParameters
