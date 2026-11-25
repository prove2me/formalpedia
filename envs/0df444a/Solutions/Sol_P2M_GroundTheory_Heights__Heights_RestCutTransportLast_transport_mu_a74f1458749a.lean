-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_mu_a74f1458749a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:33:18.642209+00:00
-- url     : https://prove2.me/submissions/bfed7f97-f0ef-45ac-a596-b1aa3cece7d8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutTransportLast
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_yRoot_fbd963f505e6

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
theorem _root_.solution (f j k : ℕ) (hk : k ≤ j) :
    restTransport f j k (k + j) (restLastEquiv j k) (RestTerms.smallBlockMu f k j .last) =
      smallMu f j k := by
  simp only [RestTerms.smallBlockMu, map_sum, transport_yRoot, smallMu, if_pos hk]
end GroundTheory.Heights₂.Heights.RestCutTransportLast
