-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_fib_1326bc32adae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:36:50.649048+00:00
-- url     : https://prove2.me/submissions/6b215d1e-6575-4072-91a4-7bfe9edb1cce

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutTransportLast
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_yRoot_fbd963f505e6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportLast_transport_zRoot_edeab7dde617
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportLast_map_vandermondeOf_0c093407b9f2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_det_rev_pow_eq_vandermondeOf_025293c6ef5f


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
theorem _root_.solution (f j k : ℕ) (hk : k ≤ j) :
    restTransport f j k (k + j) (restLastEquiv j k) (RestTerms.fibreClass f k j .last) =
      fibre f j k := by
  simp only [RestTerms.fibreClass, fibre, if_pos hk, map_prod, map_mul, map_vandermondeOf,
    transport_yRoot, transport_zRoot, vandermonde, KRest.det_rev_pow_eq_vandermondeOf]
end GroundTheory.Heights₂.Heights.RestCutTransportLast
