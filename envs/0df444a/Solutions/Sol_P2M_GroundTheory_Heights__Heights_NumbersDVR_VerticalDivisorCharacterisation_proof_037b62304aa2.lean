-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorCharacterisation_proof_037b62304aa2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:41:19.205897+00:00
-- url     : https://prove2.me/submissions/a69fb496-31df-4342-a02a-6a25514e2feb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemMinimalPrimesOfDivCycleNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinVertDivIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_form_add_f298b0f9964b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_form_of_le_646124b8182c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_component_mul_form_of_not_le_4feacf11ecb8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_multiHomog_core_be2f15a486a0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_of_unit_mul_sub_mem_e9005f30e709
import Theorems.Thm_GroundTheory_Arith_Iwasawa_IsDistinguished_ne_zero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FlagTypings_isMultiHomog_iff_8163629d7f47
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_isMultiProjPrime_iff_2b9458513c98
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_CutByForm_proof_b44260dcf444
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MinimalPrimeMultiHomog_proof_00f169244e2b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Representative_proof_61b56da860aa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_UniformiserCase_proof_3d83087b97ab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_VocabMultiHomogIdeal_proof_6afd59a7e16a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_VocabMultiHomog_proof_8751c6dffe37
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_C_eq_bot_of_not_mem_1f5ac74ee822
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_component_not_mem_53dbbac47368
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_sup_span_of_form_8aa08999bb53


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
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace VerticalDivisorCharacterisation
theorem _root_.solution : VerticalDivisorCharacterisation.Statement := by
  intro O _ _ _ K _ _ ι _ P ϖ b f g hϖ hP
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv
  constructor
  · rintro ⟨⟨α, β, hα, hβ, hb⟩, hfP, hgP, hQ⟩
    rw [← FlagTypings.isMultiHomog_iff] at hα hβ
    refine ⟨⟨α, β, hα, hβ, funext hb⟩, hfP, hgP, ?_, ?_⟩
    · intro W hW
      by_contra hϖW
      have key : ∀ (x : MRing ι O) (c : K → ℕ), IsMultiHomog x c →
          W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
          divCycle P f W = divCycle P g W := by
        intro x c hc hWm hWr
        have hWp : W.IsPrime := hWm.1.1
        have hWh : IsMultiHomogIdeal W := MinimalPrimeMultiHomog.proof O K ι _ W
          (isMultiHomogIdeal_sup_span_of_form hP.multiHomog hc) hWm
        have hPW : P ≤ W := le_sup_left.trans hWm.1.2
        obtain ⟨u, v, -, -, hu, hv, huv⟩ := hQ W
          ((BundleExamples.isMultiProjPrime_iff O W).mpr ⟨hWp, hWh, hWr⟩) hPW
          (haveI := hWp; comap_C_eq_bot_of_not_mem hϖ W hϖW)
        exact divCycle_eq_of_unit_mul_sub_mem hWp hu hv huv
      apply hW
      unfold ratDiv
      rw [sub_eq_zero]
      by_cases h1 : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W
      · exact key f α hα h1.1 h1.2
      by_cases h2 : W ∈ (P ⊔ Ideal.span {g}).minimalPrimes ∧ IsRelevant W
      · exact key g β hβ h2.1 h2.2
      unfold divCycle
      rw [dif_neg h1, dif_neg h2]
    · intro W hWp hPW hWr hϖW
      obtain ⟨W', hW'p, hW'h, hW'W, hW'max, hW'form⟩ := exists_multiHomog_core hWp
      have hPW' := hW'max P hP.multiHomog hPW
      have hW'r : IsRelevant W' := fun k =>
        let ⟨i, hi⟩ := hWr k
        ⟨i, fun h => hi (hW'W h)⟩
      have hcomap : W'.comap (C : O →+* MRing ι O) = ⊥ :=
        eq_bot_iff.mpr ((Ideal.comap_mono hW'W).trans (haveI := hWp; comap_C_eq_bot_of_not_mem hϖ W hϖW).le)
      obtain ⟨u, v, ⟨γ, hγ⟩, ⟨δ, hδ⟩, hu, hv, huv⟩ := hQ W'
        ((BundleExamples.isMultiProjPrime_iff O W').mpr ⟨hW'p, hW'h, hW'r⟩) hPW' hcomap
      rw [← FlagTypings.isMultiHomog_iff] at hγ hδ
      exact ⟨u, v, fun h => hu (hW'form u γ hγ h), fun h => hv (hW'form v δ hδ h), huv⟩
  · rintro ⟨⟨α, β, hα, hβ, hb⟩, hfP, hgP, -, hunit⟩
    refine ⟨⟨α, β, (FlagTypings.isMultiHomog_iff f α).mp hα, (FlagTypings.isMultiHomog_iff g β).mp hβ,
      fun k => congrFun hb k⟩, hfP, hgP, ?_⟩
    intro Q hQ hPQ hQO
    have hQ' : IsMultiProjPrime Q := (BundleExamples.isMultiProjPrime_iff O Q).mp hQ
    have hϖQ : (C ϖ : MRing ι O) ∉ Q := by
      intro h
      have h' : ϖ ∈ Q.comap (C : O →+* MRing ι O) := h
      rw [hQO, Ideal.mem_bot] at h'
      exact hϖ.ne_zero h'
    obtain ⟨u, v, hu, hv, huv⟩ := hunit Q hQ'.isPrime hPQ hQ'.relevant hϖQ
    obtain ⟨γ, hγ⟩ := exists_component_not_mem hu
    have hcomp := hP.multiHomog _ huv (γ + α)
    rw [map_sub, component_mul_form_add hα] at hcomp
    by_cases hβle : β ≤ γ + α
    · rw [component_mul_form_of_le hβ hβle] at hcomp
      set uγ := weightedHomogeneousComponent (blockWeight ι) γ u with huγ
      set vδ := weightedHomogeneousComponent (blockWeight ι) (γ + α - β) v with hvδ
      have hvδQ : vδ ∉ Q := by
        intro hvQ
        have h1 : f * (uγ * v - vδ * u) ∈ P := by
          have e : f * (uγ * v - vδ * u) = v * (uγ * f - vδ * g) - vδ * (u * f - v * g) := by ring
          rw [e]
          exact P.sub_mem (P.mul_mem_left _ hcomp) (P.mul_mem_left _ huv)
        have h2 : uγ * v - vδ * u ∈ Q := hPQ ((hP.isPrime.mem_or_mem h1).resolve_left hfP)
        have h3 : uγ * v ∈ Q := by
          have e : uγ * v = (uγ * v - vδ * u) + vδ * u := by ring
          rw [e]
          exact Q.add_mem h2 (Q.mul_mem_right _ hvQ)
        rcases hQ'.isPrime.mem_or_mem h3 with h | h
        exacts [hγ h, hv h]
      exact ⟨uγ, vδ,
        ⟨γ, (FlagTypings.isMultiHomog_iff _ _).mp (weightedHomogeneousComponent_isWeightedHomogeneous _ _)⟩,
        ⟨γ + α - β,
          (FlagTypings.isMultiHomog_iff _ _).mp (weightedHomogeneousComponent_isWeightedHomogeneous _ _)⟩,
        hγ, hvδQ, hcomp⟩
    · rw [component_mul_form_of_not_le hβ hβle, sub_zero] at hcomp
      rcases hP.isPrime.mem_or_mem hcomp with h | h
      exacts [absurd (hPQ h) hγ, absurd h hfP]
end VerticalDivisorCharacterisation
end GroundTheory.Heights₂.Heights.NumbersDVR
