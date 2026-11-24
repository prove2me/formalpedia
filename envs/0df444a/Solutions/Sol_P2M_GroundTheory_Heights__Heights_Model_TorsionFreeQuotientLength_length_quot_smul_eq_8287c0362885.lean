-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_TorsionFreeQuotientLength_length_quot_smul_eq_8287c0362885
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:21.02875+00:00
-- url     : https://prove2.me/submissions/9f272bba-2a3f-489d-8963-d6354939eec0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsKrullAkizuki
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PTorsionFreeQuotientLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open Module Submodule
open scoped Pointwise
open GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength
variable {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength
theorem _root_.solution {N F₀ : Type*} [AddCommGroup N] [Module R N]
    [AddCommGroup F₀] [Module R F₀] (φ : F₀ →ₗ[R] N) (hφ : Function.Injective φ) {a : R}
    (hreg : Function.Injective fun x : N => a • x)
    (hfin : IsFiniteLength R (N ⧸ LinearMap.range φ)) :
    Module.length R (N ⧸ (a • ⊤ : Submodule R N)) =
      Module.length R (F₀ ⧸ (a • ⊤ : Submodule R F₀)) := by
  set P := LinearMap.range φ
  have hPa : a • P ≤ a • ⊤ := fun x hx => by
    obtain ⟨p, -, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp hx
    exact smul_mem_pointwise_smul p a ⊤ mem_top
  have hPP : a • P ≤ P := fun x hx => by
    obtain ⟨p, hp, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp hx
    exact P.smul_mem a hp
  let f1 : (N ⧸ P) →ₗ[R] (N ⧸ a • P) := P.mapQ (a • P) (a • LinearMap.id)
    (fun x hx => by simpa using smul_mem_pointwise_smul x a P hx)
  let g1 : (N ⧸ a • P) →ₗ[R] (N ⧸ (a • ⊤ : Submodule R N)) := Submodule.factor hPa
  let f2 : (F₀ ⧸ (a • ⊤ : Submodule R F₀)) →ₗ[R] (N ⧸ a • P) := (a • ⊤ : Submodule R F₀).mapQ (a • P) φ
    (fun x hx => by
      obtain ⟨y, -, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp hx
      simpa using smul_mem_pointwise_smul (φ y) a P (LinearMap.mem_range_self φ y))
  let g2 : (N ⧸ a • P) →ₗ[R] (N ⧸ P) := Submodule.factor hPP
  have hf1 : Function.Injective f1 := by
    refine (injective_iff_map_eq_zero _).mpr fun q hq => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    simp only [f1, mapQ_apply, LinearMap.smul_apply, LinearMap.id_apply, Quotient.mk_eq_zero,
      mem_smul_pointwise_iff_exists] at hq ⊢
    obtain ⟨p, hp, hpx⟩ := hq
    rwa [← hreg hpx]
  have hg1 : Function.Surjective g1 := fun y => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have hex1 : Function.Exact f1 g1 := fun y => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro h
      have : x ∈ (a • ⊤ : Submodule R N) := (Quotient.mk_eq_zero _).mp h
      obtain ⟨b, -, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp this
      exact ⟨Submodule.Quotient.mk b, rfl⟩
    · rintro ⟨q, hq⟩
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      have hb : a • b - x ∈ a • P := (Submodule.Quotient.eq _).mp hq
      refine (Quotient.mk_eq_zero _).mpr ?_
      have h1 : a • b ∈ (a • ⊤ : Submodule R N) := smul_mem_pointwise_smul b a ⊤ mem_top
      simpa using sub_mem h1 (hPa hb)
  have hf2 : Function.Injective f2 := by
    refine (injective_iff_map_eq_zero _).mpr fun q hq => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    simp only [f2, mapQ_apply, Quotient.mk_eq_zero, mem_smul_pointwise_iff_exists] at hq ⊢
    obtain ⟨p, ⟨z, rfl⟩, hp⟩ := hq
    refine ⟨z, mem_top, hφ ?_⟩
    rw [map_smul, hp]
  have hg2 : Function.Surjective g2 := fun y => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have hex2 : Function.Exact f2 g2 := fun y => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro h
      obtain ⟨z, rfl⟩ : x ∈ P := (Quotient.mk_eq_zero _).mp h
      exact ⟨Submodule.Quotient.mk z, rfl⟩
    · rintro ⟨q, hq⟩
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      have hb : φ z - x ∈ a • P := (Submodule.Quotient.eq _).mp hq
      refine (Quotient.mk_eq_zero _).mpr ?_
      have := sub_mem (LinearMap.mem_range_self φ z) (hPP hb)
      rwa [sub_sub_cancel] at this
  have e1 := Module.length_eq_add_of_exact f1 g1 hf1 hg1 hex1
  have e2 := Module.length_eq_add_of_exact f2 g2 hf2 hg2 hex2
  rw [e1, add_comm (Module.length R (F₀ ⧸ _))] at e2
  exact WithTop.add_left_cancel (Module.length_ne_top_iff.mpr hfin) e2
end GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength
