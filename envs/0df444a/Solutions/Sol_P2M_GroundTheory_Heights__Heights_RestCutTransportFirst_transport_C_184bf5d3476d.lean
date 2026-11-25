-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_C_184bf5d3476d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:19:03.721401+00:00
-- url     : https://prove2.me/submissions/aac2b6fa-efcf-46da-9262-4bbb98c75bec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutTransportFirst

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
theorem _root_.solution (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) (c : ℚ) :
    restTransport f j k N e (C c) = C (c : ℝ) := by
  simp [restTransport, restRename]
end GroundTheory.Heights₂.Heights.RestCutTransportFirst
