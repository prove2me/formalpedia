-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutHomDecomp_proof_24695a166516
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:58:15.508582+00:00
-- url     : https://prove2.me/submissions/ac153441-0897-4664-964e-798c03a348ef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutHomDecomp
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_homogeneousComponent_mul_left_b27e51f058a8


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
namespace GroundTheory.Heights₂.Heights
namespace RestCutHomDecomp
theorem _root_.solution : RestCutHomDecomp.Statement := by
  intro f N F Q d hF hFh hNd
  unfold RestTerms.IsPowerSumDecomposition at hF ⊢
  have h := congrArg (homogeneousComponent d) hF
  rw [homogeneousComponent_eq_self hFh] at h
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hlN : l ≤ N := (Finset.mem_Icc.mp hl).2
  have hp : (RestTerms.blockPowerSum f N l τ).IsHomogeneous l := by
    unfold RestTerms.blockPowerSum
    exact IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow _ _
  rw [KRest.homogeneousComponent_mul_left hp, if_pos (hlN.trans hNd)]
end RestCutHomDecomp
end GroundTheory.Heights₂.Heights
