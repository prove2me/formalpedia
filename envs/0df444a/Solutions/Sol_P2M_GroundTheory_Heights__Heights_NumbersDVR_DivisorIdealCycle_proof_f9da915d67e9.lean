-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_DivisorIdealCycle_proof_f9da915d67e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:13:14.506729+00:00
-- url     : https://prove2.me/submissions/0d0eb5f0-e9a7-446a-aab9-faffc9948232

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivisorIdealBotUniformiser
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivisorIdealCycle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_idealCycle_eq_of_mul_mem_d9e599294e02
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_zero_of_not_mem_09583eadab34
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DivCycleMul_proof_5282581d8898
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultAtPrimeAtMinimal_proof_af70a5a37a53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SpecialQuotDim_proof_5536281ab8d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_idealCycle_4d914ac33675
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_of_mul_sub_mem_0d8c554dd825


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
namespace DivisorIdealCycle
theorem _root_.solution : DivisorIdealCycle.Statement.{u} := by
  intro R _ _ K _ _ ι _ P W f g u v hP hW hPW hg hloc hu hv huv
  funext U
  by_cases hU : U.IsPrime ∧ W ≤ U ∧ IsRelevant U
  · obtain ⟨hUp, hWU, hUrel⟩ := hU
    obtain ⟨u', v', hu'U, hloc'⟩ := hloc U hUp hWU hUrel
    have hu'W : u' ∉ W := fun h => hu'U (hWU h)
    have h1U : (1 : MRing ι R) ∉ U := (Ideal.ne_top_iff_one U).mp hUp.ne_top

    have hcross : u * v' - u' * v ∈ P := by
      have hmem : (u * v' - u' * v) * g ∈ P := by
        rw [show (u * v' - u' * v) * g = u' * (u * f - v * g) - u * (u' * f - v' * g) by ring]
        exact P.sub_mem (P.mul_mem_left _ huv) (P.mul_mem_left _ hloc')
      exact (hP.mem_or_mem hmem).resolve_right hg
    have hv'W : v' ∉ W := by
      intro h
      have hmem : u' * v ∈ W := by
        rw [show u' * v = u * v' - (u * v' - u' * v) by ring]
        exact W.sub_mem (W.mul_mem_left u h) (hPW hcross)
      exact (hW.mem_or_mem hmem).elim hu'W hv

    have hmul := congrFun (DivCycleMul.proof R K ι W u' v hW hu'W hv) U
    have hmul' := congrFun (DivCycleMul.proof R K ι W u v' hW hu hv'W) U
    have heq : divCycle W (u' * v) U = divCycle W (u * v') U :=
      divCycle_eq_of_mul_sub_mem (P := W) (W := U) (u := 1) (v := 1) h1U h1U (by
        rw [show 1 * (u' * v) - 1 * (u * v') = -(u * v' - u' * v) by ring]
        exact W.neg_mem (hPW hcross))
    have hu'0 : divCycle W u' U = 0 := divCycle_eq_zero_of_not_mem hu'U
    simp only [Pi.add_apply] at hmul hmul'

    have hv'D : v' ∈ divisorIdeal P f g := by
      rw [divisorIdeal, Submodule.mem_colon_singleton, smul_eq_mul,
        show v' * g = u' * f - (u' * f - v' * g) by ring]
      exact Submodule.sub_mem _
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f)))
        (Ideal.mem_sup_left hloc')
    have hsJ : ∀ x ∈ W ⊔ Ideal.span {v'}, 1 * x ∈ W ⊔ divisorIdeal P f g := by
      intro x hx
      rw [one_mul]
      exact sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr hv'D) W hx
    have htJ : ∀ x ∈ W ⊔ divisorIdeal P f g, u' * x ∈ W ⊔ Ideal.span {v'} := by
      intro x hx
      obtain ⟨w, hw, d, hd, rfl⟩ := Submodule.mem_sup.mp hx
      rw [divisorIdeal, Submodule.mem_colon_singleton, smul_eq_mul] at hd
      obtain ⟨p, hp, r, hr, hpr⟩ := Submodule.mem_sup.mp hd
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      have h1 : (u' * d - a * v') * g ∈ P := by
        have e : (u' * d - a * v') * g = u' * p + a * (u' * f - v' * g) := by
          calc (u' * d - a * v') * g = u' * (d * g) - a * v' * g := by ring
            _ = u' * p + a * (u' * f - v' * g) := by rw [← hpr]; ring
        rw [e]
        exact P.add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ hloc')
      have h2 : u' * d - a * v' ∈ P := (hP.mem_or_mem h1).resolve_right hg
      rw [show u' * (w + d) = (u' * w + (u' * d - a * v')) + a * v' by ring]
      exact Submodule.add_mem_sup (W.add_mem (W.mul_mem_left _ hw) (hPW h2))
        (Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩)
    have hR : idealCycle (W ⊔ divisorIdeal P f g) U = divCycle W v' U := by
      rw [divCycle_eq_idealCycle]
      exact (idealCycle_eq_of_mul_mem h1U hu'U hsJ htJ).symm
    rw [hR]
    show divCycle W v U - divCycle W u U = divCycle W v' U
    omega
  · have hcomp : ∀ J : Ideal (MRing ι R), W ≤ J → ¬ (U ∈ J.minimalPrimes ∧ IsRelevant U) := by
      rintro J hWJ ⟨h, hrel⟩
      exact hU ⟨h.1.1, hWJ.trans h.1.2, hrel⟩
    show divCycle W v U - divCycle W u U = idealCycle (W ⊔ divisorIdeal P f g) U
    unfold divCycle idealCycle
    rw [dif_neg (hcomp _ le_sup_left), dif_neg (hcomp _ le_sup_left), dif_neg (hcomp _ le_sup_left),
      sub_self]
end DivisorIdealCycle
end GroundTheory.Heights₂.Heights.NumbersDVR
