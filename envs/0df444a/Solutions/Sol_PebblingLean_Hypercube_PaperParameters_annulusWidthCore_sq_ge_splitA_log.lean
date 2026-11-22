-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.annulusWidthCore_sq_ge_splitA_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:09:20.761633+00:00
-- url     : https://prove2.me/submissions/8a85cea2-69fb-4d83-9871-d93ffde34559

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_log_le_log_two_mul_sq
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidthCore_sq_eq

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {A K : ℝ} {n : ℕ}
    (hn : 1 ≤ n) :
    A ^ 2 * ((splitA K n : ℝ) * Real.log (n : ℝ)) ≤
      (annulusWidthCore A K n) ^ 2 := by
  have hlog := log_le_log_two_mul_sq (n := n) hn
  have ha_nonneg : 0 ≤ (splitA K n : ℝ) := by positivity
  have hprod :
      (splitA K n : ℝ) * Real.log (n : ℝ) ≤
        (splitA K n : ℝ) * Real.log (2 * (n : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hlog ha_nonneg
  have hmul := mul_le_mul_of_nonneg_left hprod (sq_nonneg A)
  rw [annulusWidthCore_sq_eq (A := A) (K := K) (n := n) hn]
  exact hmul
end PebblingLean.Hypercube.PaperParameters
