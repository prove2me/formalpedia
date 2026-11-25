-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_zRoot_27fb47ecf035
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:36:17.68973+00:00
-- url     : https://prove2.me/submissions/5bea1bc3-44f8-481d-a57a-61441c219e15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutTransportFirst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_X_9220ebcde6e1

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
theorem _root_.solution (f j k : ℕ) (τ : Fin f) (i : Fin k) :
    restTransport f j k (j + k) (restFirstEquiv j k) (RestTerms.zRoot f j k .first τ i) =
      X (τ, Sum.inr i) := by
  have h : (⟨j + i.val, by have := i.isLt; omega⟩ : Fin (j + k)) = Fin.natAdd j i := Fin.ext rfl
  simp only [RestTerms.zRoot, RestTerms.zIndex, transport_X, h, restFirstEquiv,
    finSumFinEquiv_symm_apply_natAdd]
end GroundTheory.Heights₂.Heights.RestCutTransportFirst
