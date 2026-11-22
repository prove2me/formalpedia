-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.log_succ_le_log_two_add_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:09:57.756592+00:00
-- url     : https://prove2.me/submissions/7b7650b9-3dcf-4e8d-b152-d58aabbbac77

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
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) :
    Real.log (((n + 1 : ℕ) : ℝ)) ≤
      Real.log 2 + Real.log (n : ℝ) := by
  have hn_pos_nat : 0 < n := by omega
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hle_nat : n + 1 ≤ 2 * n := by omega
  have hle : ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) * (n : ℝ) := by
    exact_mod_cast hle_nat
  calc
    Real.log (((n + 1 : ℕ) : ℝ))
        ≤ Real.log ((2 : ℝ) * (n : ℝ)) := by
          exact Real.log_le_log (by positivity) hle
    _ = Real.log 2 + Real.log (n : ℝ) := by
          rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn_pos.ne']
end PebblingLean.Hypercube.PaperParameters
