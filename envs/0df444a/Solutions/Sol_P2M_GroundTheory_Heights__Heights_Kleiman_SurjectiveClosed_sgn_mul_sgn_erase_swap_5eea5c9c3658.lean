-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_sgn_mul_sgn_erase_swap_5eea5c9c3658
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:19:04.542802+00:00
-- url     : https://prove2.me/submissions/dd47d8ae-960e-47bf-a7ec-923c3116b03a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed

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
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
theorem _root_.solution {L : Finset (Fin n)} {j k : Fin n} (hj : j ∈ L) (hk : k ∈ L)
    (hjk : j ≠ k) :
    Cech.sgn L j * Cech.sgn (L.erase j) k = -(Cech.sgn L k * Cech.sgn (L.erase k) j) := by
  wlog h : j < k generalizing j k with H
  · have h' : k < j := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hjk)
    rw [H hk hj (Ne.symm hjk) h', neg_neg]
  have h1 : (L.erase j).filter (· < k) = (L.filter (· < k)).erase j := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  have h2 : (L.erase k).filter (· < j) = L.filter (· < j) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, hz⟩, hzj⟩
      exact ⟨hz, hzj⟩
    · rintro ⟨hz, hzj⟩
      exact ⟨⟨fun hzk => by subst hzk; exact lt_irrefl _ (hzj.trans h), hz⟩, hzj⟩
  have hmem : j ∈ L.filter (· < k) := Finset.mem_filter.mpr ⟨hj, h⟩
  have hc := Finset.card_erase_add_one hmem
  simp only [Cech.sgn, h1, h2]
  rw [← hc, pow_succ]
  ring
end GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
