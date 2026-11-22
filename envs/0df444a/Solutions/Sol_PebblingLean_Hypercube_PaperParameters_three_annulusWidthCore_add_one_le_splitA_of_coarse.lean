-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.three_annulusWidthCore_add_one_le_splitA_of_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:10:34.061864+00:00
-- url     : https://prove2.me/submissions/a7193f83-2c00-4db0-8e5e-1166d84471ef

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidthCore_le_sqrt_three_n_log

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution
    {A K : ℝ} {n : ℕ}
    (hA : 0 ≤ A) (hn : 2 ≤ n)
    (ha_lower : (3 : ℝ) * (n : ℝ) / 4 ≤ (splitA K n : ℝ))
    (hcoarse :
      3 * (A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1) ≤
        (3 : ℝ) * (n : ℝ) / 4) :
    3 * (annulusWidthCore A K n + 1) ≤ (splitA K n : ℝ) := by
  have hcore :=
    annulusWidthCore_le_sqrt_three_n_log
      (A := A) (K := K) (n := n) hA hn
  have hleft :
      3 * (annulusWidthCore A K n + 1) ≤
        3 * (A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1) := by
    nlinarith
  exact hleft.trans (hcoarse.trans ha_lower)
end PebblingLean.Hypercube.PaperParameters
