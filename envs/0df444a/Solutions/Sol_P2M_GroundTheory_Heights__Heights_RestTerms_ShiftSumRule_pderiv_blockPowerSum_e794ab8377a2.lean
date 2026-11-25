-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_ShiftSumRule_pderiv_blockPowerSum_e794ab8377a2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:53:02.475284+00:00
-- url     : https://prove2.me/submissions/995c47fd-a498-4470-8155-06ac83b7dfca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PShiftSumRule

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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.ShiftSumRule
namespace GroundTheory.Heights₂.Heights.RestTerms.ShiftSumRule
theorem _root_.solution (N k : ℕ) (i : Fin N) :
    pderiv ((0 : Fin 1), i) (blockPowerSum 1 N k 0) =
      (k : RootRing 1 N) * X ((0 : Fin 1), i) ^ (k - 1) := by
  classical
  rw [blockPowerSum, map_sum, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [pderiv_pow, pderiv_X_of_ne (show ((0 : Fin 1), j) ≠ ((0 : Fin 1), i) by simp [hj]), mul_zero]
  · simp
end GroundTheory.Heights₂.Heights.RestTerms.ShiftSumRule
