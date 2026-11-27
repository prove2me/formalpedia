-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CycleIntegralSection_proof_3913a604ee4a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:54:45.375364+00:00
-- url     : https://prove2.me/submissions/0825042d-a838-4f7f-9dce-3a4ae9a801e7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PCycleIntegralSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_cycleIntegral_eq_sum_9e1d366aec79

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
open MvPolynomial MeasureTheory
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace CycleIntegralSection
theorem _root_.solution : CycleIntegralSection.Statement := by
  intro n h Z u e g
  rw [cycleIntegral_eq_sum, cycleSection,
    ← Finsupp.sum_finsetSum_index (by intro W; simp) (by intro W a b; push_cast; ring)]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finsupp.sum_smul_index' (by intro W'; simp), cycleIntegral_eq_sum, Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun W' _ => ?_
  simp only [smul_eq_mul, Nat.cast_mul]
  ring
end CycleIntegralSection
end GroundTheory.Heights₂.Heights
