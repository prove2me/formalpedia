-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_sgn_mul_sgn_of_lt_ec68d02ba4cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:01:36.401798+00:00
-- url     : https://prove2.me/submissions/04758f5d-ab4d-4c08-ae86-711fe0924be0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq

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
theorem _root_.solution {K : Finset (Fin n)} {j k : Fin n} (hj : j ∈ K) (hjk : j < k) :
    Cech.sgn K k * Cech.sgn (K.erase k) j = -(Cech.sgn K j * Cech.sgn (K.erase j) k) := by
  have h1 : (K.erase k).filter (· < j) = K.filter (· < j) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨-, hz⟩, hzj⟩; exact ⟨hz, hzj⟩
    · rintro ⟨hz, hzj⟩; exact ⟨⟨(hzj.trans hjk).ne, hz⟩, hzj⟩
  have h3 : j ∈ K.filter (· < k) := Finset.mem_filter.2 ⟨hj, hjk⟩
  have h2 : ((K.erase j).filter (· < k)).card + 1 = (K.filter (· < k)).card := by
    rw [Finset.filter_erase, Finset.card_erase_add_one h3]
  unfold Cech.sgn
  rw [h1, ← h2, pow_succ]
  ring
end GroundTheory.Heights₂.Heights.Kleiman.CechDSq
