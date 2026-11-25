-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_proof_0a5f712247a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:47:44.152173+00:00
-- url     : https://prove2.me/submissions/9be76049-7773-4f3c-be9a-77f690845508

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutTransportFirst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_mu_bc6cd110a470
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_fib_c12080988bb1

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
namespace GroundTheory.Heights₂.Heights
namespace RestCutTransportFirst
theorem _root_.solution : RestCutTransportFirst.Statement := by
  intro f j k hjk
  have hn : f * (j * k) = f * j * k := (Nat.mul_assoc f j k).symm
  refine ⟨?_, ?_⟩
  · rw [RestTerms.restPolynomial, map_mul, map_pow, RestCutTransportFirst.transport_mu f j k hjk,
      RestCutTransportFirst.transport_fib f j k hjk, restInput, hn]
  · rw [map_mul, map_pow, RestCutTransportFirst.transport_mu f j k hjk,
      RestCutTransportFirst.transport_fib f j k hjk, degreeInput, hn]
end RestCutTransportFirst
end GroundTheory.Heights₂.Heights
