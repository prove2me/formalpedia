-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.radJ_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:23.190634+00:00
-- url     : https://prove2.me/submissions/5d89ff0a-cad1-4950-a4e6-1320841cbd4d

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Set Real Filter Topology
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (k : ℕ) : radJ k = Gamma (((k : ℝ) + 1) / 2) / 2 := by
  have h := integral_rpow_mul_exp_neg_rpow (p := 2) (q := (k : ℝ)) two_pos (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
  simp only [Real.rpow_natCast, Real.rpow_two] at h
  rw [radJ, h]
  ring
end ReciprocityTheory.MultiplicativeHeights
