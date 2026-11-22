-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.annulusWidthCore_ge_nine_of_coarse_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:10:45.413961+00:00
-- url     : https://prove2.me/submissions/8f76c277-ecdb-4621-9497-81b428b9a675

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidthCore_nonneg_of_A_nonneg
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidthCore_sq_ge_splitA_log

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution
    {A K : ℝ} {n : ℕ}
    (hA : 0 ≤ A) (hn : 1 ≤ n)
    (ha_lower : (3 : ℝ) * (n : ℝ) / 4 ≤ (splitA K n : ℝ))
    (hbudget :
      81 ≤ A ^ 2 * (((3 : ℝ) * (n : ℝ) / 4) *
        Real.log (n : ℝ))) :
    9 ≤ annulusWidthCore A K n := by
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_natCast_nonneg n
  have hinner :
      ((3 : ℝ) * (n : ℝ) / 4) * Real.log (n : ℝ) ≤
        (splitA K n : ℝ) * Real.log (n : ℝ) :=
    mul_le_mul_of_nonneg_right ha_lower hlog_nonneg
  have hcoarse :
      A ^ 2 * (((3 : ℝ) * (n : ℝ) / 4) *
        Real.log (n : ℝ)) ≤
        A ^ 2 * ((splitA K n : ℝ) * Real.log (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hinner (sq_nonneg A)
  have hsq :
      (9 : ℝ) ^ 2 ≤ (annulusWidthCore A K n) ^ 2 := by
    norm_num
    exact (hbudget.trans hcoarse).trans
      (annulusWidthCore_sq_ge_splitA_log (A := A) (K := K) (n := n) hn)
  exact (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 9)
    (annulusWidthCore_nonneg_of_A_nonneg
      (A := A) (K := K) (n := n) hA)).mp hsq
end PebblingLean.Hypercube.PaperParameters
