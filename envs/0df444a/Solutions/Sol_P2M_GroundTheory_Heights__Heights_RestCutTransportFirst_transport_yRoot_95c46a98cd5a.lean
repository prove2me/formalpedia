-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_yRoot_95c46a98cd5a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:32:21.733301+00:00
-- url     : https://prove2.me/submissions/26995077-3f77-4a9d-a073-2518a7713b85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutTransportFirst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_X_9220ebcde6e1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_C_184bf5d3476d

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
open GroundTheory.Heights₂.Heights.RestCutTransportFirst
namespace GroundTheory.Heights₂.Heights.RestCutTransportFirst
theorem _root_.solution (f j k : ℕ) (τ : Fin f) (i : Fin j) :
    restTransport f j k (j + k) (restFirstEquiv j k) (RestTerms.yRoot f j k .first τ i) =
      -X (τ, Sum.inl i) := by
  have h : (⟨i.val, by have := i.isLt; omega⟩ : Fin (j + k)) = Fin.castAdd k i := Fin.ext rfl
  simp only [RestTerms.yRoot, RestTerms.yIndex, RestTerms.SmallBlock.sign, map_mul, transport_C,
    transport_X, h, restFirstEquiv, finSumFinEquiv_symm_apply_castAdd]
  simp
end GroundTheory.Heights₂.Heights.RestCutTransportFirst
