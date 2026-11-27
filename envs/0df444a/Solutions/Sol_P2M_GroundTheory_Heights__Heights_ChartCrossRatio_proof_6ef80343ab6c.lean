-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartCrossRatio_proof_6ef80343ab6c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:53:08.124526+00:00
-- url     : https://prove2.me/submissions/b97363b4-7e0b-4645-a435-a3d91097e954

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ChartMonomialMemOfNotIsLive
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_chartMonomial_mem_of_not_isLive_657d083a777f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057


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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
namespace ChartCrossRatio
theorem _root_.solution : ChartCrossRatio.Statement := by
  intro ι _ _ n P D d g hg c c' j
  by_cases hc : P.IsLive c
  · by_cases hc' : P.IsLive c'
    · rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, hg.value c hc, hg.value c' hc']
      ring
    · rw [hg.dead c' hc', mul_zero, sub_zero]
      exact P.ideal.mul_mem_right _ (P.chartMonomial_mem_of_not_isLive hc' hg.pos)
  · rw [hg.dead c hc, mul_zero, zero_sub]
    exact P.ideal.neg_mem_iff.mpr
      (P.ideal.mul_mem_right _ (P.chartMonomial_mem_of_not_isLive hc hg.pos))
end ChartCrossRatio
end GroundTheory.Heights₂.Heights
