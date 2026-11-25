-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutTransportLast_proof_632e76ed1fd3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:14.012799+00:00
-- url     : https://prove2.me/submissions/e120eab8-5a3b-4352-9390-030d1ecc8b4d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutTransportLast
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_mu_a74f1458749a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_fib_1326bc32adae

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
open RestCutTransportLast
namespace GroundTheory.Heights₂.Heights
namespace RestCutTransportLast
theorem _root_.solution : RestCutTransportLast.Statement := by
  intro f j k hk
  have hn : f * (k * j) = f * j * k := by ring
  refine ⟨?_, ?_⟩
  · rw [RestTerms.restPolynomial, map_mul, map_pow, transport_mu f j k hk, transport_fib f j k hk,
      hn]
    rfl
  · rw [map_mul, map_pow, transport_mu f j k hk, transport_fib f j k hk, hn]
    rfl
end RestCutTransportLast
end GroundTheory.Heights₂.Heights
