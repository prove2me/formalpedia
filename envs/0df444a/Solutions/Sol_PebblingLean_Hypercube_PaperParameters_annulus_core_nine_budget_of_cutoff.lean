-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.annulus_core_nine_budget_of_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:10:26.886262+00:00
-- url     : https://prove2.me/submissions/53c51cdb-52dc-47c0-9ea5-81888ee016d8

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
theorem _root_.solution {A : ℝ} {n0 n : ℕ}
    (hn0_pos : 1 ≤ n0) (hn : n0 ≤ n)
    (hcutoff :
      81 ≤ A ^ 2 * (((3 : ℝ) * (n0 : ℝ) / 4) *
        Real.log (n0 : ℝ))) :
    81 ≤ A ^ 2 * (((3 : ℝ) * (n : ℝ) / 4) *
      Real.log (n : ℝ)) := by
  have hmono := nat_mul_log_mono_from_one hn0_pos hn
  have hinner :
      ((3 : ℝ) * (n0 : ℝ) / 4) * Real.log (n0 : ℝ) ≤
        ((3 : ℝ) * (n : ℝ) / 4) * Real.log (n : ℝ) := by
    nlinarith
  have hscaled :=
    mul_le_mul_of_nonneg_left hinner (sq_nonneg A)
  exact hcutoff.trans hscaled
end PebblingLean.Hypercube.PaperParameters
