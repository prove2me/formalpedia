-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutTransportPsum_proof_b44550fe9307
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:57:17.19289+00:00
-- url     : https://prove2.me/submissions/77b200ff-5fec-463e-b709-d840e7d991fe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutTransportPsum

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
namespace GroundTheory.Heights₂.Heights
namespace RestCutTransportPsum
theorem _root_.solution : RestCutTransportPsum.Statement := by
  intro f j k N e m τ
  simp only [restTransport, restRename, RestTerms.blockPowerSum, rootPsum, RingHom.comp_apply,
    map_sum, map_pow, MvPolynomial.map_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rename_X]
  exact Equiv.sum_comp e (fun i => (X (τ, i) : RootPoly f j k) ^ m)
end RestCutTransportPsum
end GroundTheory.Heights₂.Heights
