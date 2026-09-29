-- Prove2me | solution 1 for ValuationSubring.isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b3124be4-45a4-54fe-a1b7-c09a46b45a1d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EmbCountDvr

open IsLocalRing IsDedekindDomain

section general

variable {L : Type*} [Field L]

theorem isUnit_iff_inv_mem (V : ValuationSubring L) (x : V) (hx0 : (x : L) ≠ 0) :
    IsUnit x ↔ (x : L)⁻¹ ∈ V := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨y, hy⟩ := hx.exists_left_inv
    have hyx : (y : L) * (x : L) = 1 := by
      have := congrArg (Subtype.val) hy
      simpa using this
    rw [← eq_inv_of_mul_eq_one_left hyx]
    exact y.2
  · exact isUnit_iff_exists_inv.mpr ⟨⟨_, hx⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

theorem mem_maximalIdeal_iff_inv_not_mem (V : ValuationSubring L) (x : V) (hx0 : (x : L) ≠ 0) :
    x ∈ maximalIdeal V ↔ (x : L)⁻¹ ∉ V := by
  rw [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff, isUnit_iff_inv_mem V x hx0]

theorem mem_nonunits_iff_eq_zero_or_inv_not_mem (V : ValuationSubring L) (x : L) :
    x ∈ V.nonunits ↔ x = 0 ∨ x⁻¹ ∉ V := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  constructor
  · rintro ⟨hxV, hmax⟩
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · exact Or.inr ((mem_maximalIdeal_iff_inv_not_mem V ⟨x, hxV⟩ hx0).mp hmax)
  · rintro (rfl | hinv)
    · exact ⟨V.zero_mem, by
        have : (⟨(0 : L), V.zero_mem⟩ : V) = 0 := rfl
        rw [this]; exact Ideal.zero_mem _⟩
    · have hx0 : x ≠ 0 := by rintro rfl; exact hinv (by rw [inv_zero]; exact V.zero_mem)
      have hxV : x ∈ V := (V.mem_or_inv_mem x).resolve_right hinv
      exact ⟨hxV, (mem_maximalIdeal_iff_inv_not_mem V ⟨x, hxV⟩ hx0).mpr hinv⟩

theorem inertiaDeg_maximalIdeal_eq_one_of_isLocalization {R : Type*} [CommRing R]
    (p : Ideal R) [p.IsMaximal] (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ]
    [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ] :
    p.inertiaDeg' (maximalIdeal Rₚ) = 1 := by
  haveI : (maximalIdeal Rₚ).LiesOver p :=
    ⟨(IsLocalization.AtPrime.under_maximalIdeal Rₚ p).symm⟩
  rw [Ideal.inertiaDeg_algebraMap]
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal p Rₚ
  have he : ∀ c, e c = algebraMap (R ⧸ p) (Rₚ ⧸ maximalIdeal Rₚ) c := by
    intro c
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    rfl
  let e' : (R ⧸ p) ≃ₗ[R ⧸ p] (Rₚ ⧸ maximalIdeal Rₚ) :=
    { e with
      map_smul' := fun c x => by
        change e (c * x) = c • e x
        rw [map_mul, Algebra.smul_def, he] }
  rw [← e'.finrank_eq, Module.finrank_self]

end general

structure Over (C : Type*) [CommRing C] [IsLocalRing C] {F : Type*} [Field F] [Algebra C F]
    (B : ValuationSubring F) : Prop where
  mem : ∀ c : C, algebraMap C F c ∈ B
  nonunit_iff : ∀ c : C, algebraMap C F c ∈ B.nonunits ↔ c ∈ maximalIdeal C

section dict

variable {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
variable {F : Type*} [Field F] [Algebra K F] [Algebra C F] [IsScalarTower C K F]

abbrev overAlgebra (B : ValuationSubring F) (h : ∀ c : C, algebraMap C F c ∈ B) : Algebra C B :=
  ((algebraMap C F).codRestrict B h).toAlgebra

theorem coe_algebraMap_overAlgebra (B : ValuationSubring F) (h : ∀ c : C, algebraMap C F c ∈ B)
    (c : C) :
    letI := overAlgebra B h
    ((algebraMap C B c : B) : F) = algebraMap C F c := rfl

theorem isScalarTower_overAlgebra (B : ValuationSubring F) (h : ∀ c : C, algebraMap C F c ∈ B) :
    letI := overAlgebra B h
    IsScalarTower C B F := by
  letI := overAlgebra B h
  exact IsScalarTower.of_algebraMap_eq fun a => rfl

include K in
theorem algebraMap_injective : Function.Injective (algebraMap C F) := by
  rw [IsScalarTower.algebraMap_eq C K F]
  exact (algebraMap K F).injective.comp (IsFractionRing.injective C K)

include K in
theorem algebraMap_overAlgebra_injective (B : ValuationSubring F)
    (h : ∀ c : C, algebraMap C F c ∈ B) :
    letI := overAlgebra B h
    Function.Injective (algebraMap C B) := by
  letI := overAlgebra B h
  intro a b hab
  have := congrArg (fun z : B => (z : F)) hab
  exact algebraMap_injective K this

theorem comap_maximalIdeal_overAlgebra (B : ValuationSubring F) (h : Over C B) :
    letI := overAlgebra B h.mem
    (maximalIdeal B).comap (algebraMap C B) = maximalIdeal C := by
  letI := overAlgebra B h.mem
  ext c
  rw [Ideal.mem_comap, ← h.nonunit_iff, ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

theorem liesOver_overAlgebra (B : ValuationSubring F) (h : Over C B) :
    letI := overAlgebra B h.mem
    (maximalIdeal B).LiesOver (maximalIdeal C) := by
  letI := overAlgebra B h.mem
  exact ⟨(comap_maximalIdeal_overAlgebra B h).symm⟩

theorem mem_of_mem_integralClosure (B : ValuationSubring F) (h : ∀ c : C, algebraMap C F c ∈ B)
    {y : F} (hy : y ∈ integralClosure C F) : y ∈ B := by
  letI := overAlgebra B h
  haveI := isScalarTower_overAlgebra B h
  have hyB : IsIntegral B y := ((mem_integralClosure_iff C F).mp hy).tower_top
  obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff F).mp inferInstance hyB
  rw [← hz]
  exact z.2

include K in

theorem ne_top_of_over (B : ValuationSubring F) (h : Over C B) : B ≠ ⊤ := by
  intro hB
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible C
  have hϖ0 : algebraMap C F ϖ ≠ 0 := (map_ne_zero_iff _ (algebraMap_injective K)).mpr hϖ.ne_zero
  have hmem : algebraMap C F ϖ ∈ B.nonunits :=
    (h.nonunit_iff ϖ).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit)
  rcases (mem_nonunits_iff_eq_zero_or_inv_not_mem B _).mp hmem with h0 | hinv
  · exact hϖ0 h0
  · apply hinv
    rw [hB]
    exact ValuationSubring.mem_top _

theorem maximalIdeal_ne_bot : maximalIdeal C ≠ ⊥ :=
  IsDiscreteValuationRing.not_a_field C

theorem coe_algebraMap_integralClosure (c : C) :
    ((algebraMap C (integralClosure C F) c : integralClosure C F) : F) = algebraMap C F c := rfl

include K in
theorem algebraMap_integralClosure_injective :
    Function.Injective (algebraMap C (integralClosure C F)) := by
  intro a b hab
  have := congrArg (fun z : integralClosure C F => (z : F)) hab
  exact algebraMap_injective K this

include K in
theorem isTorsionFree_integralClosure : Module.IsTorsionFree C (integralClosure C F) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro r c hrc
  rw [Algebra.smul_def] at hrc
  rcases mul_eq_zero.mp hrc with h | h
  · exact Or.inl (algebraMap_integralClosure_injective K (by rw [h, map_zero]))
  · exact Or.inr h

include K in

theorem liesOver_maximalIdeal (v : HeightOneSpectrum (integralClosure C F)) :
    v.asIdeal.LiesOver (maximalIdeal C) := by
  haveI := isTorsionFree_integralClosure K (F := F) (C := C)
  refine ⟨(IsLocalRing.eq_maximalIdeal ?_).symm⟩
  have hne : v.asIdeal.under C ≠ ⊥ := fun h0 =>
    v.ne_bot (Ideal.eq_bot_of_comap_eq_bot h0)
  exact Ring.DimensionLEOne.maximalOfPrime hne (Ideal.IsPrime.under C v.asIdeal)

noncomputable def toOver (B : ValuationSubring F) (h : ∀ c : C, algebraMap C F c ∈ B) :
    integralClosure C F →+* B :=
  (algebraMap (integralClosure C F) F).codRestrict B fun y => mem_of_mem_integralClosure B h y.2

@[scoped simp] theorem coe_toOver (B : ValuationSubring F) (h : ∀ c : C, algebraMap C F c ∈ B)
    (s : integralClosure C F) : ((toOver B h s : B) : F) = (s : F) := rfl

noncomputable def center (B : ValuationSubring F) (h : ∀ c : C, algebraMap C F c ∈ B) :
    Ideal (integralClosure C F) :=
  (maximalIdeal B).comap (toOver B h)

theorem mem_center_iff (B : ValuationSubring F) (h : ∀ c : C, algebraMap C F c ∈ B)
    (s : integralClosure C F) :
    s ∈ center B h ↔ (s : F) ∈ B.nonunits := by
  rw [center, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

scoped instance center_isPrime (B : ValuationSubring F) (h : ∀ c : C, algebraMap C F c ∈ B) :
    (center B h).IsPrime :=
  Ideal.comap_isPrime _ _

include K in
theorem center_ne_bot (B : ValuationSubring F) (h : Over C B) : center B h.mem ≠ ⊥ := by
  intro h0
  have h1 : (center B h.mem).comap (algebraMap C (integralClosure C F)) = ⊥ := by
    rw [h0]; exact Ideal.comap_bot_of_injective _ (algebraMap_integralClosure_injective K)
  have h2 : (center B h.mem).comap (algebraMap C (integralClosure C F)) = maximalIdeal C := by
    ext c
    rw [Ideal.mem_comap, mem_center_iff, coe_algebraMap_integralClosure, h.nonunit_iff]
  exact maximalIdeal_ne_bot (h2 ▸ h1)

noncomputable def vOf (B : ValuationSubring F) (h : Over C B) :
    HeightOneSpectrum (integralClosure C F) :=
  ⟨center B h.mem, inferInstance, center_ne_bot K B h⟩

section finite

variable [FiniteDimensional K F] [Algebra.IsSeparable K F]

include K in
theorem isFractionRing_integralClosure : IsFractionRing (integralClosure C F) F :=
  integralClosure.isFractionRing_of_finite_extension K F

include K in
theorem isDedekindDomain_integralClosure : IsDedekindDomain (integralClosure C F) :=
  integralClosure.isDedekindDomain C K F

include K in
theorem finite_integralClosure : Module.Finite C (integralClosure C F) :=
  IsIntegralClosure.finite C K F (integralClosure C F)

noncomputable def W (v : HeightOneSpectrum (integralClosure C F)) : ValuationSubring F :=
  letI := isFractionRing_integralClosure K (F := F) (C := C)
  letI := isDedekindDomain_integralClosure K (F := F) (C := C)
  HeightOneSpectrum.valuationSubringAtPrime F v

theorem W_def (v : HeightOneSpectrum (integralClosure C F)) :
    letI := isFractionRing_integralClosure K (F := F) (C := C)
    letI := isDedekindDomain_integralClosure K (F := F) (C := C)
    W K v = HeightOneSpectrum.valuationSubringAtPrime F v := rfl

end finite

end dict

end EmbCountDvr
p2m_reactivate "P2MW.S_ValuationSubring_isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable.EmbCountDvr"

namespace EmbCountDvr

open IsLocalRing IsDedekindDomain

section main

variable {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
variable {F : Type*} [Field F] [Algebra K F] [Algebra C F] [IsScalarTower C K F]
variable [FiniteDimensional K F] [Algebra.IsSeparable K F]

include K in
theorem main (B : ValuationSubring F) (h : Over C B) : IsDiscreteValuationRing ↥B := by
  haveI := isFractionRing_integralClosure K (F := F) (C := C)
  haveI := isDedekindDomain_integralClosure K (F := F) (C := C)
  let v : HeightOneSpectrum (integralClosure C F) := vOf K B h

  have hle : HeightOneSpectrum.valuationSubringAtPrime F v ≤ B := by
    rintro y ⟨a, s, hs, rfl⟩
    refine B.mul_mem _ _ (mem_of_mem_integralClosure B h.mem a.2) ?_
    have hs' : s ∉ center B h.mem := hs
    have hs0 : (s : F) ≠ 0 := by
      rintro h0
      apply hs'
      have : s = 0 := Subtype.ext h0
      rw [this]; exact Ideal.zero_mem _
    have := (mem_maximalIdeal_iff_inv_not_mem B (toOver B h.mem s) hs0).not.mp
      (fun hm => hs' (Ideal.mem_comap.mpr hm))
    simpa using this
  have heq : HeightOneSpectrum.valuationSubringAtPrime F v = B :=
    ValuationSubring.eq_of_le_of_ne_top _ hle (ne_top_of_over K B h)
  rw [← heq]
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (integralClosure C F)
    v.ne_bot (HeightOneSpectrum.valuationSubringAtPrime F v)

end main
p2m_reactivate "P2MW.S_ValuationSubring_isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable.EmbCountDvr"

end EmbCountDvr
p2m_reactivate "P2MW.S_ValuationSubring_isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable.EmbCountDvr"

open IsLocalRing in
theorem solution
    {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
    {F : Type*} [Field F] [Algebra K F] [Algebra C F] [IsScalarTower C K F]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (B : ValuationSubring F) (hCB : ∀ c : C, algebraMap C F c ∈ B)
    (hCBmax : ∀ c : C, algebraMap C F c ∈ B.nonunits ↔ c ∈ maximalIdeal C) :
    IsDiscreteValuationRing ↥B :=
  EmbCountDvr.main K B ⟨hCB, hCBmax⟩

end S_ValuationSubring_isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable
end P2MW
export P2MW.S_ValuationSubring_isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable (solution)
