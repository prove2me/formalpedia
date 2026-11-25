-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_fib_c12080988bb1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:40:43.232418+00:00
-- url     : https://prove2.me/submissions/a14c2d02-14ac-4ee5-898b-149d70bbbff1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutTransportFirst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_map_vandermondeOf_f16575da4a7f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_yRoot_95c46a98cd5a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutTransportFirst_transport_zRoot_27fb47ecf035
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
open GroundTheory.Heights₂.Heights.RestCutTransportFirst
namespace GroundTheory.Heights₂.Heights.RestCutTransportFirst
theorem _root_.solution (f j k : ℕ) (hjk : j < k) :
    restTransport f j k (j + k) (restFirstEquiv j k) (RestTerms.fibreClass f j k .first) =
      fibre f j k := by
  have hkj : ¬ k ≤ j := by omega
  simp only [RestTerms.fibreClass, map_prod, map_mul, map_vandermondeOf, transport_yRoot,
    transport_zRoot, fibre, if_neg hkj, vandermonde, KRest.det_rev_pow_eq_vandermondeOf]
end GroundTheory.Heights₂.Heights.RestCutTransportFirst
