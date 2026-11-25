-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_eq_of_mul_sub_mem_0d8c554dd825
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:56:21.451993+00:00
-- url     : https://prove2.me/submissions/fa24de0a-394f-4329-b09b-edc13aa4b04e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_mul_mem_ff40c44cee89
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localized_eq_of_mul_mem_35ad3b84a6a8

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
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {P : Ideal (MRing ι R)} {f g u v : MRing ι R}
    {W : Ideal (MRing ι R)} (hu : u ∉ W) (hv : v ∉ W) (h : u * f - v * g ∈ P) :
    divCycle P f W = divCycle P g W := by
  have h1 : ∀ x ∈ P ⊔ Ideal.span {f}, u * x ∈ P ⊔ Ideal.span {g} := by
    intro x hx
    obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have e : u * (p + c * f) = (u * p + c * (u * f - v * g)) + (c * v) * g := by ring
    rw [e]
    exact Submodule.add_mem_sup (P.add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ h))
      (Ideal.mem_span_singleton'.mpr ⟨c * v, rfl⟩)
  have h2 : ∀ x ∈ P ⊔ Ideal.span {g}, v * x ∈ P ⊔ Ideal.span {f} := by
    intro x hx
    obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have e : v * (p + c * g) = (v * p - c * (u * f - v * g)) + (c * u) * f := by ring
    rw [e]
    exact Submodule.add_mem_sup (P.sub_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ h))
      (Ideal.mem_span_singleton'.mpr ⟨c * u, rfl⟩)
  unfold divCycle
  by_cases hf : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W
  · have hg : W ∈ (P ⊔ Ideal.span {g}).minimalPrimes ∧ IsRelevant W :=
      ⟨mem_minimalPrimes_of_mul_mem hu hv h1 h2 hf.1, hf.2⟩
    rw [dif_pos hf, dif_pos hg]
    have : W.IsPrime := hf.1.1.1
    unfold multAt
    rw [length_localized_eq_of_mul_mem hu hv h1 h2]
  · have hg : ¬ (W ∈ (P ⊔ Ideal.span {g}).minimalPrimes ∧ IsRelevant W) := fun hg =>
      hf ⟨mem_minimalPrimes_of_mul_mem hv hu h2 h1 hg.1, hg.2⟩
    rw [dif_neg hf, dif_neg hg]
end GroundTheory.Heights₂.Heights.NumbersDVR
