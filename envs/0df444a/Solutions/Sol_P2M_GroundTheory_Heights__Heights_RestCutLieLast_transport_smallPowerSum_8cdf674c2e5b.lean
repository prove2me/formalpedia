-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutLieLast_transport_smallPowerSum_8cdf674c2e5b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:58:42.526919+00:00
-- url     : https://prove2.me/submissions/f201958b-57d3-4c44-a27f-cbde866d4cf1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutLieLast

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
open GroundTheory.Heights₂.Heights.RestCutLieLast
namespace GroundTheory.Heights₂.Heights.RestCutLieLast
theorem _root_.solution (f j k m : ℕ) (τ : Fin f) :
    restTransport f j k (k + j) (restLastEquiv j k) (RestTerms.smallPowerSum f k j .last m τ) =
      ∑ b : Fin k, X (τ, Sum.inr b) ^ m := by
  unfold RestTerms.smallPowerSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have he : restLastEquiv j k ⟨j + b.val, by have := b.isLt; omega⟩ = Sum.inr b := by
    have : (finCongr (Nat.add_comm k j)) ⟨j + b.val, by have := b.isLt; omega⟩ = Fin.natAdd j b :=
      Fin.ext rfl
    simp only [restLastEquiv, Equiv.trans_apply, this, finSumFinEquiv_symm_apply_natAdd]
  simp [restTransport, restRename, RestTerms.yRoot, RestTerms.yIndex, RestTerms.SmallBlock.sign,
    he]
end GroundTheory.Heights₂.Heights.RestCutLieLast
