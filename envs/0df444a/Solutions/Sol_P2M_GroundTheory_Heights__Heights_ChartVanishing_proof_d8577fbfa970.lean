-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartVanishing_proof_d8577fbfa970
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:04:13.131375+00:00
-- url     : https://prove2.me/submissions/b3397b90-3963-4af4-9b30-0b21fcba55b4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroTer
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_evalHom_apply_58ec575df9f4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_chartMonomial_mem_of_not_live_bf792022ff30
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_exists_ne_zero_of_live_658b61e9df41
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartVanishing_eq_zero_of_live_2f8a88aac417

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
open GroundTheory.Heights₂.Heights.ChartVanishing
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.ChartVanishing
theorem _root_.solution : ChartVanishing.Statement := by
  intro ι _ _ n P D d g hg z hz c
  by_cases hc : P.IsLive c
  · constructor
    · intro h0
      by_contra hm
      obtain ⟨j, hj⟩ := exists_ne_zero_of_live hg hz hc hm
      exact hj (h0 j)
    · exact eq_zero_of_live hg hz hc
  · refine ⟨fun _ ↦ hz.2 _ (chartMonomial_mem_of_not_live P hc hg.pos), fun _ j ↦ ?_⟩
    rw [hg.dead c hc j, ← evalHom_apply, map_zero]
end GroundTheory.Heights₂.Heights.ChartVanishing
