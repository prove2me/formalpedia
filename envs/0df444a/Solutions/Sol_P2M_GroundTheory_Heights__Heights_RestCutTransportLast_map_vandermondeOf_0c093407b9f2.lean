-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutTransportLast_map_vandermondeOf_0c093407b9f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:59:00.123178+00:00
-- url     : https://prove2.me/submissions/5d73412e-b287-4982-8296-78166f3c00d8

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
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) {m : ℕ}
    (v : Fin m → R) : g (RestTerms.vandermondeOf v) = RestTerms.vandermondeOf fun i => g (v i) := by
  simp only [RestTerms.vandermondeOf, map_prod, map_sub]
end GroundTheory.Heights₂.Heights.RestCutTransportLast
