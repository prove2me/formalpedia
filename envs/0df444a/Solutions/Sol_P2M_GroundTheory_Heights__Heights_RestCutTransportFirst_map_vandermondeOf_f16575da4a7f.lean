-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_map_vandermondeOf_f16575da4a7f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:58:45.952831+00:00
-- url     : https://prove2.me/submissions/d4156015-b506-4778-bd32-c487e957b057

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
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ}
    (v : Fin m → R) : φ (RestTerms.vandermondeOf v) = RestTerms.vandermondeOf (fun i => φ (v i)) := by
  simp [RestTerms.vandermondeOf, map_prod, map_sub]
end GroundTheory.Heights₂.Heights.RestCutTransportFirst
