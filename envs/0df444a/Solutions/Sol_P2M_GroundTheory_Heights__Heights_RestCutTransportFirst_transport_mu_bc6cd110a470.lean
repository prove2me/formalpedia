-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_mu_bc6cd110a470
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:36:47.783159+00:00
-- url     : https://prove2.me/submissions/fdbee6fc-fd24-4c80-a2fe-c33dde68525b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutTransportFirst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_yRoot_95c46a98cd5a

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
theorem _root_.solution (f j k : ℕ) (hjk : j < k) :
    restTransport f j k (j + k) (restFirstEquiv j k) (RestTerms.smallBlockMu f j k .first) =
      smallMu f j k := by
  have hkj : ¬ k ≤ j := by omega
  simp only [RestTerms.smallBlockMu, map_sum, transport_yRoot, smallMu, if_neg hkj]
end GroundTheory.Heights₂.Heights.RestCutTransportFirst
