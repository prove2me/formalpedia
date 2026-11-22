-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.width_const_budget_of_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:10:31.795805+00:00
-- url     : https://prove2.me/submissions/5306d5c0-e5d4-4640-9fe7-f260d76022cb

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_nat_mul_log_mono_from_one

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {K : ℝ} {n0 n : ℕ}
    (hK : 0 ≤ K)
    (hn0_pos : 1 ≤ n0)
    (hn : n0 ≤ n)
    (hcutoff :
      Real.log 128 + 4 * Real.log 2 ≤
        (K / 30 * Real.log 2) *
          Real.sqrt ((n0 : ℝ) * Real.log (n0 : ℝ))) :
    Real.log 128 + 4 * Real.log 2 ≤
      (K / 30 * Real.log 2) *
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
  have hcore := nat_mul_log_mono_from_one hn0_pos hn
  have hsqrt := Real.sqrt_le_sqrt hcore
  have hlog2_nonneg : 0 ≤ Real.log 2 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hcoeff_nonneg : 0 ≤ K / 30 * Real.log 2 := by positivity
  have hmono :
      (K / 30 * Real.log 2) *
          Real.sqrt ((n0 : ℝ) * Real.log (n0 : ℝ)) ≤
        (K / 30 * Real.log 2) *
          Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hsqrt hcoeff_nonneg
  exact hcutoff.trans hmono
end PebblingLean.Hypercube.PaperParameters
