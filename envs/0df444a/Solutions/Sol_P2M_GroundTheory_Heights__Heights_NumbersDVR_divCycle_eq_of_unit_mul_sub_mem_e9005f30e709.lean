-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_of_unit_mul_sub_mem_e9005f30e709
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:21.372998+00:00
-- url     : https://prove2.me/submissions/1fc3594b-daf7-4b8f-9691-72103b4465e8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemMinimalPrimesOfDivCycleNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinVertDivIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedQuot_eq_of_mul_le_8d87d4368795
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mul_mem_sup_span_of_sub_mem_409f1971e60c

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
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {P W : Ideal (MRing ι R)} (hW : W.IsPrime) {f g u v : MRing ι R}
    (hu : u ∉ W) (hv : v ∉ W) (h : u * f - v * g ∈ P) : divCycle P f W = divCycle P g W := by
  have h' : v * g - u * f ∈ P := by
    have := P.neg_mem h
    rwa [neg_sub] at this
  have claim : ∀ W' : Ideal (MRing ι R), W'.IsPrime → W' ≤ W →
      (P ⊔ Ideal.span {f} ≤ W' ↔ P ⊔ Ideal.span {g} ≤ W') := by
    intro W' hW' hle
    simp only [sup_le_iff, Ideal.span_singleton_le_iff_mem]
    constructor
    · rintro ⟨hP, hf⟩
      refine ⟨hP, (hW'.mem_or_mem ?_).resolve_left fun h'' => hv (hle h'')⟩
      have e : v * g = u * f - (u * f - v * g) := by ring
      rw [e]
      exact W'.sub_mem (W'.mul_mem_left u hf) (hP h)
    · rintro ⟨hP, hg⟩
      refine ⟨hP, (hW'.mem_or_mem ?_).resolve_left fun h'' => hu (hle h'')⟩
      have e : u * f = (u * f - v * g) + v * g := by ring
      rw [e]
      exact W'.add_mem (hP h) (W'.mul_mem_left v hg)
  have hmin : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ↔ W ∈ (P ⊔ Ideal.span {g}).minimalPrimes := by
    constructor
    · rintro ⟨⟨hp, h1⟩, hm⟩
      exact ⟨⟨hp, (claim W hW le_rfl).1 h1⟩,
        fun y hy hyx => hm ⟨hy.1, (claim y hy.1 hyx).2 hy.2⟩ hyx⟩
    · rintro ⟨⟨hp, h1⟩, hm⟩
      exact ⟨⟨hp, (claim W hW le_rfl).2 h1⟩,
        fun y hy hyx => hm ⟨hy.1, (claim y hy.1 hyx).1 hy.2⟩ hyx⟩
  haveI := hW
  have hmult : multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
    unfold multAt
    rw [← length_localizedQuot_eq_of_mul_le
        (I := (P ⊔ Ideal.span {f}) ⊓ (P ⊔ Ideal.span {g})) inf_le_left hu
        (fun x hx => Ideal.mem_inf.mpr ⟨Ideal.mul_mem_left _ _ hx, mul_mem_sup_span_of_sub_mem h hx⟩),
      length_localizedQuot_eq_of_mul_le inf_le_right hv
        (fun x hx => Ideal.mem_inf.mpr ⟨mul_mem_sup_span_of_sub_mem h' hx, Ideal.mul_mem_left _ _ hx⟩)]
  unfold divCycle
  by_cases hc : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W
  · have hc' : W ∈ (P ⊔ Ideal.span {g}).minimalPrimes ∧ IsRelevant W := ⟨hmin.1 hc.1, hc.2⟩
    rw [dif_pos hc, dif_pos hc']
    exact congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ)) hmult
  · have hc' : ¬ (W ∈ (P ⊔ Ideal.span {g}).minimalPrimes ∧ IsRelevant W) :=
      fun h'' => hc ⟨hmin.2 h''.1, h''.2⟩
    rw [dif_neg hc, dif_neg hc']
end GroundTheory.Heights₂.Heights.NumbersDVR
