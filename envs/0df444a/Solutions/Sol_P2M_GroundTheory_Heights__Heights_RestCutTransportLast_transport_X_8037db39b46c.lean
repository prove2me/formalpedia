-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_X_8037db39b46c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:57:51.847083+00:00
-- url     : https://prove2.me/submissions/95c29932-010c-4b68-9317-5dc74b7cb199

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutTransportLast

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
theorem _root_.solution (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) (p : Fin f × Fin N) :
    restTransport f j k N e (X p) = X (p.1, e p.2) := by
  simp [restTransport, restRename]
end GroundTheory.Heights₂.Heights.RestCutTransportLast
