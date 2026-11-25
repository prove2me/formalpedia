-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_zRoot_edeab7dde617
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:32:39.327809+00:00
-- url     : https://prove2.me/submissions/1f2a110e-3992-42c8-9a94-f95a005f8d7e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutTransportLast
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_X_8037db39b46c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportLast_lastEquiv_top_87eb9e6ee819

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
open GroundTheory.Heights₂.Heights.RestCutTransportLast
namespace GroundTheory.Heights₂.Heights.RestCutTransportLast
theorem _root_.solution (f j k : ℕ) (τ : Fin f) (i : Fin j) :
    restTransport f j k (k + j) (restLastEquiv j k) (RestTerms.zRoot f k j .last τ i) =
      X (τ, Sum.inl i) := by
  simp only [RestTerms.zRoot, RestTerms.zIndex, transport_X, lastEquiv_top]
end GroundTheory.Heights₂.Heights.RestCutTransportLast
