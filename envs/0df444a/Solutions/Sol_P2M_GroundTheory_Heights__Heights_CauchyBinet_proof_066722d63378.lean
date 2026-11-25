-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CauchyBinet_proof_066722d63378
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:51:12.114829+00:00
-- url     : https://prove2.me/submissions/f00c8c90-26df-4e0e-9925-07a72f949611

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_det_mul_eq_sum_e0cc8465dd90
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_det_submatrix_eq_zero_cec33daaf8a4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_minor_mul_a10f27a6654c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_sum_reindex_e19d84f6339c

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
open Matrix Finset Equiv
namespace GroundTheory.Heights₂.Heights
namespace CauchyBinet
theorem _root_.solution : CauchyBinet.Statement := by
  intro R _ j N A B
  rw [CauchyBinetAlt.det_mul_eq_sum, CauchyBinetAlt.sum_reindex _ (fun p hp => by
    rw [CauchyBinetAlt.det_submatrix_eq_zero A hp, mul_zero])]
  exact Finset.sum_congr rfl fun I _ => (CauchyBinetAlt.minor_mul A B I).symm
end CauchyBinet
end GroundTheory.Heights₂.Heights
