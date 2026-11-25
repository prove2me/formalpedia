-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingLocal_proof_56cc4fc2aa55
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:34:10.675802+00:00
-- url     : https://prove2.me/submissions/0082fafb-a341-4c84-8d0f-bc6b236d17a8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_homLocRing_form_not_mem_76f04394fb55

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace HomLocRingLocal
theorem _root_.solution (hloc : HomLocRingIsLocal.Statement.{u})
    (hnoeth : HomLocRingNoetherian.Statement.{u}) (hdim : HomLocRingDimLe.Statement.{u}) :
    HomLocRingLocal.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ P hP c x hx hxP W hW hWrel
  have := hP.isPrime
  have hWp : W.IsPrime := hW.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hxW : x ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  obtain ⟨hlocal, hunit⟩ := hloc O K ι P W hWp hPW
  have hnoe := hnoeth O K ι P W hP.multiHomog hWp hWrel hPW
  refine ⟨hlocal, hnoe, le_antisymm ?_ ?_⟩
  · refine (hdim O K ι P W hP.multiHomog hWp hWrel hPW).trans ?_
    have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
    exact_mod_cast h1
  · obtain ⟨g, hg, hgW⟩ := homLocRing_form_not_mem hWp hWrel c
    have hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P x) /
        algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P g) ∈
          homLocRing P W :=
      Subring.subset_closure ⟨c, x, g, hx, hg, hgW, rfl⟩
    have hnu : ¬ IsUnit (⟨_, hz⟩ : homLocRing P W) :=
      fun h => (hunit c x g hx hg hgW hz).mp h hxW
    have hne : (⟨_, hz⟩ : homLocRing P W) ≠ 0 := by
      intro h0
      have h1 := congrArg Subtype.val h0
      simp only [ZeroMemClass.coe_zero, div_eq_zero_iff,
        IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h1
      rcases h1 with h1 | h1
      · exact hxP h1
      · exact hgW (hPW h1)
    have hlt : (⊥ : Ideal (homLocRing P W)) < IsLocalRing.maximalIdeal (homLocRing P W) := by
      refine bot_lt_iff_ne_bot.mpr fun h => hne ?_
      have hm := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      rwa [h, Ideal.mem_bot] at hm
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    have h3 : (1 : ℕ∞) ≤ (IsLocalRing.maximalIdeal (homLocRing P W)).height :=
      le_trans le_add_self h2
    exact_mod_cast h3
end HomLocRingLocal
end GroundTheory.Heights₂.Heights.NumbersDVR
