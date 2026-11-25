-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_X_9220ebcde6e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:58:18.381689+00:00
-- url     : https://prove2.me/submissions/4c2e4150-64a5-4d1c-86a9-65094f78e32d

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
theorem _root_.solution (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) (p : Fin f × Fin N) :
    restTransport f j k N e (X p) = X (p.1, e p.2) := by
  simp [restTransport, restRename]
end GroundTheory.Heights₂.Heights.RestCutTransportFirst
