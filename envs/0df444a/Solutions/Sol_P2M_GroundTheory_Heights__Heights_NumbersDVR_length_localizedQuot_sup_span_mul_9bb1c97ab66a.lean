-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedQuot_sup_span_mul_9bb1c97ab66a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:15.522831+00:00
-- url     : https://prove2.me/submissions/caa7a380-7571-45df-b260-697a6203b976

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul

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
variable {A : Type*} [CommRing A]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (P W : Ideal A) [P.IsPrime] [W.IsPrime] {x : A} (y : A)
    (hx : x ∉ P) :
    Module.length (Localization.AtPrime W)
        (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {x * y}))) =
      Module.length (Localization.AtPrime W)
          (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {y}))) +
        Module.length (Localization.AtPrime W)
          (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {x}))) := by
  have hle : P ⊔ Ideal.span {x * y} ≤ P ⊔ Ideal.span {x} :=
    sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self x))) P
  let g₁ : (A ⧸ (P ⊔ Ideal.span {y})) →ₗ[A] A ⧸ (P ⊔ Ideal.span {x * y}) :=
    Submodule.mapQ _ _ (LinearMap.mulLeft A x) (fun a ha => by
      obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      show x * (p + c * y) ∈ P ⊔ Ideal.span {x * y}
      have e : x * (p + c * y) = x * p + c * (x * y) := by ring
      rw [e]
      exact Submodule.add_mem_sup (P.mul_mem_left _ hp) (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩))
  let g₂ : (A ⧸ (P ⊔ Ideal.span {x * y})) →ₗ[A] A ⧸ (P ⊔ Ideal.span {x}) :=
    Submodule.mapQ _ _ LinearMap.id (fun a ha => hle ha)
  have hinj : Function.Injective g₁ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    induction z using Submodule.Quotient.induction_on with | _ a => ?_
    rw [LinearMap.mem_ker] at hz
    simp only [g₁, Submodule.mapQ_apply, LinearMap.mulLeft_apply,
      Submodule.Quotient.mk_eq_zero] at hz
    simp only [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    obtain ⟨p, hp, r, hr, hpr⟩ := Submodule.mem_sup.mp hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have hm : x * (a - c * y) ∈ P := by
      have e : x * (a - c * y) = p := by linear_combination hpr.symm
      rw [e]; exact hp
    have ha : a - c * y ∈ P := (‹P.IsPrime›.mem_or_mem hm).resolve_left hx
    have e : a = (a - c * y) + c * y := by ring
    rw [e]
    exact Submodule.add_mem_sup ha (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩)
  have hsurj : Function.Surjective g₂ := by
    intro z
    induction z using Submodule.Quotient.induction_on with | _ a => ?_
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  have hex : Function.Exact g₁ g₂ := by
    intro z
    induction z using Submodule.Quotient.induction_on with | _ a => ?_
    simp only [g₂, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
      Set.mem_range]
    constructor
    · intro ha
      obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      refine ⟨Submodule.Quotient.mk c, ?_⟩
      simp only [g₁, Submodule.mapQ_apply, LinearMap.mulLeft_apply]
      rw [Submodule.Quotient.eq]
      have e : x * c - (p + c * x) = -p := by ring
      rw [e]
      exact Submodule.mem_sup_left (P.neg_mem hp)
    · rintro ⟨z, hz⟩
      induction z using Submodule.Quotient.induction_on with | _ c => ?_
      simp only [g₁, Submodule.mapQ_apply, LinearMap.mulLeft_apply] at hz
      rw [Submodule.Quotient.eq] at hz
      have e : a = -(x * c - a) + c * x := by ring
      rw [e]
      exact Submodule.add_mem _ (Submodule.neg_mem _ (hle hz))
        (Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩))
  exact Module.length_eq_add_of_exact (R := Localization.AtPrime W)
    (LocalizedModule.map W.primeCompl g₁) (LocalizedModule.map W.primeCompl g₂)
    (LocalizedModule.map_injective _ _ hinj) (LocalizedModule.map_surjective _ _ hsurj)
    (LocalizedModule.map_exact _ _ _ hex)
end GroundTheory.Heights₂.Heights.NumbersDVR
