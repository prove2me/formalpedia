-- Prove2me | solution 1 for ValuationSubring.finsum_ramificationIdx_mul_inertiaDeg_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/3a06b5dd-e4e1-52ed-85d9-100bab7ba21a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_finsum_ramificationIdx_mul_inertiaDeg_eq_finrank

open IsLocalRing IsDedekindDomain

namespace ValuationSubring
p2m_export "ValuationSubring" "comap subtype coe_mem_nonunits_iff mem_comap ext zero_mem nonunits mem_nonunits_iff mem_top eq_of_le_of_ne_top mul_mem mem_or_inv_mem algebra valuation inclusion comap_comap"
p2m_open "ValuationSubring"
namespace FundamentalEquality

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (A : ValuationSubring K)

theorem isUnit_iff_inv_mem {L : Type*} [Field L] (C : ValuationSubring L) (x : C)
    (hx0 : (x : L) ≠ 0) : IsUnit x ↔ (x : L)⁻¹ ∈ C := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨y, hy⟩ := hx.exists_left_inv
    have hyx : (y : L) * (x : L) = 1 := by
      have := congrArg (Subtype.val) hy
      simpa using this
    rw [← eq_inv_of_mul_eq_one_left hyx]
    exact y.2
  · exact isUnit_iff_exists_inv.mpr ⟨⟨_, hx⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

theorem mem_maximalIdeal_iff_inv_not_mem {L : Type*} [Field L] (C : ValuationSubring L) (x : C)
    (hx0 : (x : L) ≠ 0) : x ∈ maximalIdeal C ↔ (x : L)⁻¹ ∉ C := by
  rw [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff, isUnit_iff_inv_mem C x hx0]

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

def Over (B : ValuationSubring F) : Prop := ∀ x : K, algebraMap K F x ∈ B ↔ x ∈ A

variable {A}

abbrev overAlgebra (B : ValuationSubring F) (h : Over A B) : Algebra A B :=
  (((algebraMap K F).comp A.subtype).codRestrict B fun a => (h a).mpr a.2).toAlgebra

theorem coe_algebraMap_overAlgebra (B : ValuationSubring F) (h : Over A B) (a : A) :
    letI := overAlgebra B h
    ((algebraMap A B a : B) : F) = algebraMap K F a := rfl

theorem isScalarTower_overAlgebra (B : ValuationSubring F) (h : Over A B) :
    letI := overAlgebra B h
    IsScalarTower A B F := by
  letI := overAlgebra B h
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  change algebraMap K F a = ((algebraMap A B a : B) : F)
  rfl

theorem algebraMap_overAlgebra_injective (B : ValuationSubring F) (h : Over A B) :
    letI := overAlgebra B h
    Function.Injective (algebraMap A B) := by
  letI := overAlgebra B h
  intro a b hab
  have := congrArg (fun z : B => (z : F)) hab
  simp only [coe_algebraMap_overAlgebra] at this
  exact Subtype.ext ((algebraMap K F).injective this)

theorem comap_maximalIdeal_overAlgebra (B : ValuationSubring F) (h : Over A B) :
    letI := overAlgebra B h
    (maximalIdeal B).comap (algebraMap A B) = maximalIdeal A := by
  letI := overAlgebra B h
  ext a
  rw [Ideal.mem_comap]
  by_cases ha0 : (a : K) = 0
  · have : a = 0 := Subtype.ext ha0
    subst this
    simp
  have hb0 : ((algebraMap A B a : B) : F) ≠ 0 := by
    rw [coe_algebraMap_overAlgebra]
    exact (map_ne_zero _).mpr ha0
  rw [mem_maximalIdeal_iff_inv_not_mem B _ hb0, mem_maximalIdeal_iff_inv_not_mem A _ ha0,
    coe_algebraMap_overAlgebra, ← map_inv₀, h]

theorem mem_of_mem_integralClosure (B : ValuationSubring F) (h : Over A B)
    {y : F} (hy : y ∈ integralClosure A F) : y ∈ B := by
  letI := overAlgebra B h
  haveI := isScalarTower_overAlgebra B h
  have hyB : IsIntegral B y := ((mem_integralClosure_iff A F).mp hy).tower_top
  obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff F).mp inferInstance hyB
  rw [← hz]
  exact z.2

theorem ne_top_of_over [IsDiscreteValuationRing A] (B : ValuationSubring F) (h : Over A B) :
    B ≠ ⊤ := by
  intro hB
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hϖ0 : (ϖ : K) ≠ 0 := fun h0 => hϖ.ne_zero (Subtype.ext h0)
  have hϖA : (ϖ : K)⁻¹ ∉ A := by
    rw [← mem_maximalIdeal_iff_inv_not_mem A ϖ hϖ0]
    exact hϖ.not_isUnit
  apply hϖA
  rw [← h, hB]
  exact mem_top _

variable (A)

theorem maximalIdeal_ne_bot [IsDiscreteValuationRing A] : maximalIdeal A ≠ ⊥ :=
  IsDiscreteValuationRing.not_a_field A

theorem coe_algebraMap_integralClosure (a : A) :
    ((algebraMap A (integralClosure A F) a : integralClosure A F) : F) = algebraMap K F a := rfl

theorem algebraMap_integralClosure_injective :
    Function.Injective (algebraMap A (integralClosure A F)) := by
  intro a b hab
  have := congrArg (fun z : integralClosure A F => (z : F)) hab
  simp only [coe_algebraMap_integralClosure] at this
  exact Subtype.ext ((algebraMap K F).injective this)

theorem isTorsionFree_integralClosure : Module.IsTorsionFree A (integralClosure A F) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro r c hrc
  rw [Algebra.smul_def] at hrc
  rcases mul_eq_zero.mp hrc with h | h
  · exact Or.inl (algebraMap_integralClosure_injective A (by rw [h, map_zero]))
  · exact Or.inr h

attribute [local instance] isTorsionFree_integralClosure

theorem liesOver_maximalIdeal [IsDiscreteValuationRing A]
    (v : HeightOneSpectrum (integralClosure A F)) :
    v.asIdeal.LiesOver (maximalIdeal A) := by
  refine ⟨(IsLocalRing.eq_maximalIdeal ?_).symm⟩
  have hne : v.asIdeal.under A ≠ ⊥ := fun h0 =>
    v.ne_bot (Ideal.eq_bot_of_comap_eq_bot h0)
  exact Ring.DimensionLEOne.maximalOfPrime hne (Ideal.IsPrime.under A v.asIdeal)

attribute [local instance] liesOver_maximalIdeal

variable {A}

noncomputable def toOver (B : ValuationSubring F) (h : Over A B) : integralClosure A F →+* B :=
  (algebraMap (integralClosure A F) F).codRestrict B fun y => mem_of_mem_integralClosure B h y.2

@[scoped simp] theorem coe_toOver (B : ValuationSubring F) (h : Over A B) (s : integralClosure A F) :
    ((toOver B h s : B) : F) = (s : F) := rfl

noncomputable def center (B : ValuationSubring F) (h : Over A B) : Ideal (integralClosure A F) :=
  (maximalIdeal B).comap (toOver B h)

theorem mem_center_iff (B : ValuationSubring F) (h : Over A B) (s : integralClosure A F) :
    s ∈ center B h ↔ (s : F) ∈ B.nonunits := by
  rw [center, Ideal.mem_comap, ← coe_mem_nonunits_iff]
  rfl

scoped instance center_isPrime (B : ValuationSubring F) (h : Over A B) : (center B h).IsPrime :=
  Ideal.comap_isPrime _ _

theorem center_ne_bot [IsDiscreteValuationRing A] (B : ValuationSubring F) (h : Over A B) :
    center B h ≠ ⊥ := by
  letI := overAlgebra B h
  intro h0
  have h1 : (center B h).comap (algebraMap A (integralClosure A F)) = ⊥ := by
    rw [h0]; exact Ideal.comap_bot_of_injective _ (algebraMap_integralClosure_injective A)
  have h2 : (center B h).comap (algebraMap A (integralClosure A F)) = maximalIdeal A := by
    rw [center, Ideal.comap_comap, ← comap_maximalIdeal_overAlgebra B h]
    congr 1
  exact maximalIdeal_ne_bot A (h2 ▸ h1)

noncomputable def vOf [IsDiscreteValuationRing A] (B : ValuationSubring F) (h : Over A B) :
    HeightOneSpectrum (integralClosure A F) :=
  ⟨center B h, inferInstance, center_ne_bot B h⟩

section finite

variable (A)
variable [FiniteDimensional K F]

theorem isFractionRing_integralClosure : IsFractionRing (integralClosure A F) F :=
  integralClosure.isFractionRing_of_finite_extension K F

attribute [local instance] isFractionRing_integralClosure

variable [IsDiscreteValuationRing A] [Module.Finite A (integralClosure A F)]

theorem isDedekindDomain_integralClosure : IsDedekindDomain (integralClosure A F) := by
  have hN : IsNoetherianRing (integralClosure A F) :=
    isNoetherian_of_tower A (isNoetherian_of_isNoetherianRing_of_finite A (integralClosure A F))
  have hI : IsIntegrallyClosed (integralClosure A F) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  have hD : Ring.DimensionLEOne (integralClosure A F) := inferInstance
  exact (isDedekindDomain_iff (integralClosure A F) F).mpr
    ⟨inferInstance, hN, hD, fun {x} hx => (isIntegrallyClosed_iff F).mp hI hx⟩

attribute [local instance] isDedekindDomain_integralClosure

noncomputable abbrev W (v : HeightOneSpectrum (integralClosure A F)) : ValuationSubring F :=
  HeightOneSpectrum.valuationSubringAtPrime F v

theorem isDiscreteValuationRing_W (v : HeightOneSpectrum (integralClosure A F)) :
    IsDiscreteValuationRing (W A v) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (integralClosure A F)
    v.ne_bot (W A v)

theorem coe_algebraMap_W (v : HeightOneSpectrum (integralClosure A F)) (s : integralClosure A F) :
    ((algebraMap (integralClosure A F) (W A v) s : W A v) : F) = (s : F) := rfl

theorem over_W (v : HeightOneSpectrum (integralClosure A F)) : Over A (W A v) := by
  intro x
  constructor
  · intro hx
    by_contra hxA
    have hx0 : x ≠ 0 := by rintro rfl; exact hxA A.zero_mem
    have hxinv : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hxA
    have hmax : (⟨x⁻¹, hxinv⟩ : A) ∈ maximalIdeal A := by
      rw [mem_maximalIdeal_iff_inv_not_mem A _ (inv_ne_zero hx0)]
      simpa using hxA
    have h1 : algebraMap A (integralClosure A F) ⟨x⁻¹, hxinv⟩ ∈ v.asIdeal := by
      rw [(liesOver_maximalIdeal A v).over] at hmax
      exact Ideal.mem_comap.mp hmax
    have h2 := (IsLocalization.AtPrime.to_map_mem_maximal_iff (W A v) v.asIdeal _).mpr h1
    have h3 : IsUnit (algebraMap (integralClosure A F) (W A v)
        (algebraMap A (integralClosure A F) ⟨x⁻¹, hxinv⟩)) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K F x, hx⟩, Subtype.ext ?_⟩
      change ((algebraMap (integralClosure A F) (W A v)
        (algebraMap A (integralClosure A F) ⟨x⁻¹, hxinv⟩) : W A v) : F) * algebraMap K F x = 1
      rw [coe_algebraMap_W, coe_algebraMap_integralClosure]
      change algebraMap K F x⁻¹ * algebraMap K F x = 1
      rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp h2) h3
  · intro hx
    have : algebraMap K F x = ((algebraMap (integralClosure A F) (W A v)
        (algebraMap A (integralClosure A F) ⟨x, hx⟩) : W A v) : F) := by
      rw [coe_algebraMap_W]
      rfl
    rw [this]
    exact SetLike.coe_mem _

variable {A}

theorem W_vOf_le (B : ValuationSubring F) (h : Over A B) : W A (vOf B h) ≤ B := by
  rintro y ⟨a, s, hs, rfl⟩
  refine B.mul_mem _ _ (mem_of_mem_integralClosure B h a.2) ?_
  have hs' : s ∉ center B h := hs
  have hs0 : (s : F) ≠ 0 := by
    rintro h0
    apply hs'
    have : s = 0 := Subtype.ext h0
    rw [this]; exact Ideal.zero_mem _
  have := (mem_maximalIdeal_iff_inv_not_mem B (toOver B h s) hs0).not.mp
    (fun hm => hs' (Ideal.mem_comap.mpr hm))
  simpa using this

theorem W_vOf_eq (B : ValuationSubring F) (h : Over A B) : W A (vOf B h) = B :=
  ValuationSubring.eq_of_le_of_ne_top _ (W_vOf_le B h) (ne_top_of_over B h)

theorem vOf_W (v : HeightOneSpectrum (integralClosure A F)) : vOf (W A v) (over_W A v) = v := by
  apply HeightOneSpectrum.ext
  ext s
  change s ∈ center (W A v) (over_W A v) ↔ s ∈ v.asIdeal
  rw [mem_center_iff, ← coe_algebraMap_W A v s, coe_mem_nonunits_iff,
    IsLocalization.AtPrime.to_map_mem_maximal_iff (W A v) v.asIdeal]

variable (A)

noncomputable def overEquiv :
    {B : ValuationSubring F // Over A B} ≃ HeightOneSpectrum (integralClosure A F) where
  toFun B := vOf B.1 B.2
  invFun v := ⟨W A v, over_W A v⟩
  left_inv B := Subtype.ext (W_vOf_eq B.1 B.2)
  right_inv v := vOf_W v

noncomputable def hosEquiv : HeightOneSpectrum (integralClosure A F) ≃
    ↥(IsDedekindDomain.primesOverFinset (maximalIdeal A) (integralClosure A F)) where
  toFun v := ⟨v.asIdeal, (IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot A)
    (integralClosure A F)).mpr ⟨v.isPrime, liesOver_maximalIdeal A v⟩⟩
  invFun P :=
    haveI := ((IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot A)
      (integralClosure A F)).mp P.2).1
    haveI := ((IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot A)
      (integralClosure A F)).mp P.2).2
    ⟨P.1, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot (maximalIdeal_ne_bot A) P.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem ramificationIdx_mul_inertiaDeg_W (v : HeightOneSpectrum (integralClosure A F)) :
    letI := overAlgebra (W A v) (over_W A v)
    (maximalIdeal A).ramificationIdx' (maximalIdeal (W A v)) *
      (maximalIdeal A).inertiaDeg' (maximalIdeal (W A v)) =
    (maximalIdeal A).ramificationIdx' v.asIdeal * (maximalIdeal A).inertiaDeg' v.asIdeal := by
  letI : Algebra A (W A v) := overAlgebra (W A v) (over_W A v)
  haveI : IsScalarTower A (integralClosure A F) (W A v) :=
    IsScalarTower.of_algebraMap_eq fun a => Subtype.ext rfl
  haveI : IsDiscreteValuationRing (W A v) := isDiscreteValuationRing_W A v
  have hmapS : Ideal.map (algebraMap (integralClosure A F) (W A v)) v.asIdeal =
      maximalIdeal (W A v) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal v.asIdeal (W A v)
  have hmW0 : maximalIdeal (W A v) ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  haveI : (maximalIdeal (W A v)).LiesOver v.asIdeal :=
    ⟨(IsLocalization.AtPrime.under_maximalIdeal (W A v) v.asIdeal).symm⟩
  have he : (maximalIdeal A).ramificationIdx' (maximalIdeal (W A v)) =
      (maximalIdeal A).ramificationIdx' v.asIdeal *
        v.asIdeal.ramificationIdx' (maximalIdeal (W A v)) :=
    Ideal.ramificationIdx_algebra_tower (by rw [hmapS]; exact hmW0)
      (by
        rw [Ne, Ideal.map_eq_bot_iff_of_injective (algebraMap_overAlgebra_injective _ _)]
        exact maximalIdeal_ne_bot A)
      hmapS.le
  have he1 : v.asIdeal.ramificationIdx' (maximalIdeal (W A v)) = 1 := by
    rw [← hmapS]
    exact Ideal.ramificationIdx_map_self_eq_one
      (by rw [hmapS]; exact (maximalIdeal.isMaximal _).ne_top) (by rw [hmapS]; exact hmW0)
  have hf : (maximalIdeal A).inertiaDeg' (maximalIdeal (W A v)) =
      (maximalIdeal A).inertiaDeg' v.asIdeal * v.asIdeal.inertiaDeg' (maximalIdeal (W A v)) :=
    Ideal.inertiaDeg_algebra_tower _ _ _
  have hf1 : v.asIdeal.inertiaDeg' (maximalIdeal (W A v)) = 1 :=
    inertiaDeg_maximalIdeal_eq_one_of_isLocalization v.asIdeal (W A v)
  rw [he, he1, hf, hf1, mul_one, mul_one]

theorem main :
    {B : ValuationSubring F | ∀ x : K, algebraMap K F x ∈ B ↔ x ∈ A}.Finite ∧
    (∀ B : ValuationSubring F, (∀ x : K, algebraMap K F x ∈ B ↔ x ∈ A) →
      IsDiscreteValuationRing B) ∧
    ∑ᶠ B : {B : ValuationSubring F // ∀ x : K, algebraMap K F x ∈ B ↔ x ∈ A},
      (letI : Algebra A B.1 := (((algebraMap K F).comp A.subtype).codRestrict B.1
          fun a => (B.2 a).mpr a.2).toAlgebra
       (maximalIdeal A).ramificationIdx' (maximalIdeal B.1) *
         (maximalIdeal A).inertiaDeg' (maximalIdeal B.1)) =
      Module.finrank K F := by
  let ε := (overEquiv A (F := F)).trans (hosEquiv A)
  haveI : Fintype {B : ValuationSubring F // Over A B} := Fintype.ofEquiv _ ε.symm
  refine ⟨?_, ?_, ?_⟩
  · exact Set.finite_coe_iff.mp (Finite.of_fintype {B : ValuationSubring F // Over A B})
  · intro B h
    rw [← W_vOf_eq B h]
    exact isDiscreteValuationRing_W A _
  · change ∑ᶠ B : {B : ValuationSubring F // Over A B},
      (letI := overAlgebra B.1 B.2
       (maximalIdeal A).ramificationIdx' (maximalIdeal B.1) *
         (maximalIdeal A).inertiaDeg' (maximalIdeal B.1)) = Module.finrank K F
    rw [finsum_eq_sum_of_fintype,
      ← Ideal.sum_ramification_inertia (R := A) (integralClosure A F) K F (maximalIdeal_ne_bot A),
      ← Finset.sum_coe_sort
        (IsDedekindDomain.primesOverFinset (maximalIdeal A) (integralClosure A F))]
    symm
    refine Fintype.sum_equiv ε.symm _ _ ?_
    intro P
    exact (ramificationIdx_mul_inertiaDeg_W A ((hosEquiv (F := F) A).symm P)).symm

end finite

end FundamentalEquality
p2m_reactivate "P2MW.S_ValuationSubring_finsum_ramificationIdx_mul_inertiaDeg_eq_finrank.ValuationSubring.FundamentalEquality"
end ValuationSubring
p2m_reactivate "P2MW.S_ValuationSubring_finsum_ramificationIdx_mul_inertiaDeg_eq_finrank.ValuationSubring.FundamentalEquality P2MW.S_ValuationSubring_finsum_ramificationIdx_mul_inertiaDeg_eq_finrank.ValuationSubring"

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F]
    (A : ValuationSubring K) [IsDiscreteValuationRing A]
    [Module.Finite A (integralClosure A F)] :
    {B : ValuationSubring F | ∀ x : K, algebraMap K F x ∈ B ↔ x ∈ A}.Finite ∧
    (∀ B : ValuationSubring F, (∀ x : K, algebraMap K F x ∈ B ↔ x ∈ A) →
      IsDiscreteValuationRing B) ∧
    ∑ᶠ B : {B : ValuationSubring F // ∀ x : K, algebraMap K F x ∈ B ↔ x ∈ A},
      (letI : Algebra A B.1 := (((algebraMap K F).comp A.subtype).codRestrict B.1
          fun a => (B.2 a).mpr a.2).toAlgebra
       (IsLocalRing.maximalIdeal A).ramificationIdx' (IsLocalRing.maximalIdeal B.1) *
         (IsLocalRing.maximalIdeal A).inertiaDeg' (IsLocalRing.maximalIdeal B.1)) =
      Module.finrank K F :=
  ValuationSubring.FundamentalEquality.main A

end S_ValuationSubring_finsum_ramificationIdx_mul_inertiaDeg_eq_finrank
end P2MW
export P2MW.S_ValuationSubring_finsum_ramificationIdx_mul_inertiaDeg_eq_finrank (solution)
