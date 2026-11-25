-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_C_e6973f950734
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:57:56.203315+00:00
-- url     : https://prove2.me/submissions/f3fa41f0-a40d-4219-854f-29d57679a403

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
theorem _root_.solution (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k) (c : ℚ) :
    restTransport f j k N e (C c) = C (c : ℝ) := by
  simp [restTransport, restRename]
end GroundTheory.Heights₂.Heights.RestCutTransportLast
