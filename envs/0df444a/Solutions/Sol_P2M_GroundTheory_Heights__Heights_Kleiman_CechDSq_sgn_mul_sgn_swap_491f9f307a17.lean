-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_sgn_mul_sgn_swap_491f9f307a17
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:37:41.732241+00:00
-- url     : https://prove2.me/submissions/efe143f6-15d6-41c8-93b4-bee5d84209a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_sgn_mul_sgn_of_lt_ec68d02ba4cc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.CechDSq
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman.CechDSq
theorem _root_.solution {K : Finset (Fin n)} {j k : Fin n} (hk : k ∈ K) (hj : j ∈ K) (hne : j ≠ k) :
    Cech.sgn K k * Cech.sgn (K.erase k) j = -(Cech.sgn K j * Cech.sgn (K.erase j) k) := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact sgn_mul_sgn_of_lt hj h
  · rw [sgn_mul_sgn_of_lt hk h, neg_neg]
end GroundTheory.Heights₂.Heights.Kleiman.CechDSq
