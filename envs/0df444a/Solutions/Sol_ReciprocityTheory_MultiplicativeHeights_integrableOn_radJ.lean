-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.integrableOn_radJ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:42.022813+00:00
-- url     : https://prove2.me/submissions/f572de33-518a-4e21-a1b7-2d85779f9059

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
theorem _root_.solution (k : ℕ) :
    IntegrableOn (fun r : ℝ => r ^ k * exp (-r ^ 2)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_rpow (p := 2) (s := (k : ℝ)) (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]) two_pos
  refine h.congr_fun (fun r _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, Real.rpow_two]
end ReciprocityTheory.MultiplicativeHeights
