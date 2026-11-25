-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_weight_groupWeight_apply_bef25cb93b13
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:41:15.209114+00:00
-- url     : https://prove2.me/submissions/2a36aa26-e688-47be-8f6d-0aede1a36933

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {k n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (d : Fin k × Fin n →₀ ℕ) (i : Fin k) :
    Finsupp.weight (groupWeight k n) d i = Finsupp.weight (inGroup (n := n) i) d := by
  classical
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun ij _ => ?_
  simp only [groupWeight, inGroup, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases h : ij.1 = i
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]
end GroundTheory.Heights₂.Heights
