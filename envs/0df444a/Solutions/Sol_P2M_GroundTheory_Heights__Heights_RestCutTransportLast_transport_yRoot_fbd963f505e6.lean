-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_yRoot_fbd963f505e6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:57.952152+00:00
-- url     : https://prove2.me/submissions/20548061-d664-4879-b513-cd8803697d5b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutTransportLast
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_X_8037db39b46c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_C_e6973f950734
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportLast_lastEquiv_bottom_671ead235411

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
theorem _root_.solution (f j k : ℕ) (τ : Fin f) (i : Fin k) :
    restTransport f j k (k + j) (restLastEquiv j k) (RestTerms.yRoot f k j .last τ i) =
      X (τ, Sum.inr i) := by
  simp only [RestTerms.yRoot, RestTerms.yIndex, RestTerms.SmallBlock.sign, map_mul, transport_C,
    transport_X, lastEquiv_bottom]
  simp
end GroundTheory.Heights₂.Heights.RestCutTransportLast
