-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.nat_mul_log_mono_from_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:59:56.566257+00:00
-- url     : https://prove2.me/submissions/d9683dff-2400-45dc-8637-be434bb8e912

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {n0 n : ℕ}
    (hn0_pos : 1 ≤ n0)
    (hn : n0 ≤ n) :
    (n0 : ℝ) * Real.log (n0 : ℝ) ≤
      (n : ℝ) * Real.log (n : ℝ) := by
  have hn0_pos_nat : 0 < n0 := by omega
  have hn0_pos_real : 0 < (n0 : ℝ) := by exact_mod_cast hn0_pos_nat
  have hnreal : (n0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog_le : Real.log (n0 : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hn0_pos_real hnreal
  have hlog0_nonneg : 0 ≤ Real.log (n0 : ℝ) :=
    Real.log_natCast_nonneg n0
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  exact mul_le_mul hnreal hlog_le hlog0_nonneg hn_nonneg
end PebblingLean.Hypercube.PaperParameters
