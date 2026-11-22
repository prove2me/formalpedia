-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.annulusWidthCore_le_sqrt_three_n_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:09:18.364798+00:00
-- url     : https://prove2.me/submissions/a4f0086c-7200-46b4-8a04-b865b8e88b4e

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitA_real_le_n
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_log_two_mul_sq_le_three_log

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {A K : ℝ} {n : ℕ}
    (hA : 0 ≤ A) (hn : 2 ≤ n) :
    annulusWidthCore A K n ≤
      A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) := by
  have hsplit := splitA_real_le_n (K := K) (n := n)
  have hlog := log_two_mul_sq_le_three_log (n := n) hn
  have hlog_nonneg : 0 ≤ Real.log (2 * (n : ℝ) ^ 2) := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
    have hge : (1 : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by nlinarith
    exact Real.log_nonneg hge
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have harg :
      (splitA K n : ℝ) * Real.log (2 * (n : ℝ) ^ 2) ≤
        3 * (n : ℝ) * Real.log (n : ℝ) := by
    calc
      (splitA K n : ℝ) * Real.log (2 * (n : ℝ) ^ 2)
          ≤ (n : ℝ) * Real.log (2 * (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hsplit hlog_nonneg
      _ ≤ (n : ℝ) * (3 * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog hn_nonneg
      _ = 3 * (n : ℝ) * Real.log (n : ℝ) := by ring
  unfold annulusWidthCore
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt harg) hA
end PebblingLean.Hypercube.PaperParameters
