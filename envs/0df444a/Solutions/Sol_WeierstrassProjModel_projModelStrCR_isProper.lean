-- Prove2me | solution 1 for WeierstrassProjModel.projModelStrCR_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/61644128-3010-51e7-a6f4-16ba9f9572f6

import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_projModelStrCR_isProper

set_option autoImplicit false

namespace HomogeneousIdealQuotientGrading
p2m_export "HomogeneousIdealQuotientGrading" "quotGradingSubmodule mem_quotGradingSubmodule_iff mk_mem_quotGradingSubmodule"
p2m_open "HomogeneousIdealQuotientGrading"

section FiniteTypeEngine

variable {ι A σ τ : Type*}
variable [CommRing A] [AddMonoid ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [SetLike.GradedMonoid 𝒜]
variable (I : Ideal A)
variable [SetLike τ (A ⧸ I)] [AddSubmonoidClass τ (A ⧸ I)] (ℬ : ι → τ) [SetLike.GradedMonoid ℬ]

private theorem finiteType_gradeZero_quotient_of_mk_mem
    (hmem0 : ∀ a : A, a ∈ 𝒜 0 → Ideal.Quotient.mk I a ∈ ℬ 0)
    (hFT : Algebra.FiniteType (𝒜 0) A) :
    Algebra.FiniteType (ℬ 0) (A ⧸ I) := by
  classical
  obtain ⟨s, hs⟩ := hFT.out
  refine ⟨⟨s.image (Ideal.Quotient.mk I), ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have ha : a ∈ Algebra.adjoin (𝒜 0) (s : Set A) := hs.ge Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
      exact Algebra.subset_adjoin (by
        simpa using Finset.mem_image_of_mem (Ideal.Quotient.mk I) hy)
  | algebraMap r =>
      have hr : Ideal.Quotient.mk I (algebraMap (𝒜 0) A r) ∈ ℬ 0 := hmem0 _ r.2
      exact Subalgebra.algebraMap_mem _ (⟨_, hr⟩ : ℬ 0)
  | add x y hx hy ihx ihy =>
      rw [map_add]; exact add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
      rw [map_mul]; exact mul_mem ihx ihy

end FiniteTypeEngine

section BaseUpgrade

variable {ι R A : Type*}
variable [CommRing R] [CommRing A] [Algebra R A] [AddMonoid ι]
variable (𝒜 : ι → Submodule R A) [SetLike.GradedMonoid 𝒜]

private theorem isScalarTower_gradeZero : IsScalarTower R (𝒜 0) A :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private theorem finiteType_gradeZero_of_finiteType_base (hFT : Algebra.FiniteType R A) :
    Algebra.FiniteType (𝒜 0) A := by
  haveI : IsScalarTower R (𝒜 0) A := isScalarTower_gradeZero 𝒜
  haveI := hFT
  exact Algebra.FiniteType.of_restrictScalars_finiteType R (𝒜 0) A

end BaseUpgrade

section QuotGradingSubmoduleDegreeZero

variable {ι R A : Type*}
variable [CommRing R] [CommRing A] [Algebra R A] [AddMonoid ι]
variable (𝒜 : ι → Submodule R A) [SetLike.GradedMonoid 𝒜]
variable (I : Ideal A)

private theorem quotGradingSubmodule_degreeZero_finiteType (hFT : Algebra.FiniteType (𝒜 0) A) :
    Algebra.FiniteType ((quotGradingSubmodule 𝒜 I) 0) (A ⧸ I) :=
  finiteType_gradeZero_quotient_of_mk_mem 𝒜 I (quotGradingSubmodule 𝒜 I)
    (fun _ ha => mk_mem_quotGradingSubmodule 𝒜 I ha) hFT

private scoped instance quotGradingSubmoduleDegreeZeroFiniteType [Algebra.FiniteType (𝒜 0) A] :
    Algebra.FiniteType ((quotGradingSubmodule 𝒜 I) 0) (A ⧸ I) :=
  quotGradingSubmodule_degreeZero_finiteType 𝒜 I ‹_›

private theorem quotGradingSubmodule_degreeZero_finiteType_of_base (hFT : Algebra.FiniteType R A) :
    Algebra.FiniteType ((quotGradingSubmodule 𝒜 I) 0) (A ⧸ I) :=
  quotGradingSubmodule_degreeZero_finiteType 𝒜 I
    (finiteType_gradeZero_of_finiteType_base 𝒜 hFT)

end QuotGradingSubmoduleDegreeZero

section MvPolynomialVenue

open MvPolynomial

private scoped instance homogeneousSubmoduleDegreeZeroFiniteType (σs R : Type*) [Finite σs] [CommRing R] :
    Algebra.FiniteType ((homogeneousSubmodule σs R) 0) (MvPolynomial σs R) :=
  finiteType_gradeZero_of_finiteType_base (homogeneousSubmodule σs R) inferInstance

private theorem quotGradingSubmodule_homogeneousSubmodule_degreeZero_finiteType
    (σs R : Type*) [Finite σs] [CommRing R] (I : Ideal (MvPolynomial σs R)) :
    Algebra.FiniteType
      ((quotGradingSubmodule (homogeneousSubmodule σs R) I) 0)
      (MvPolynomial σs R ⧸ I) :=
  inferInstance

end MvPolynomialVenue

section DegreeZeroEngine

variable {ι R A : Type*}
variable [CommRing R] [CommRing A] [Algebra R A] [AddMonoid ι]
variable (𝒜 : ι → Submodule R A) [SetLike.GradedMonoid 𝒜]
variable (I : Ideal A)

private def gradeZeroQuotAlgHom : (𝒜 0) →ₐ[R] ((quotGradingSubmodule 𝒜 I) 0) where
  toFun x := ⟨Ideal.Quotient.mk I (x : A), mk_mem_quotGradingSubmodule 𝒜 I x.2⟩
  map_one' := Subtype.ext <| by
    show Ideal.Quotient.mk I ((1 : 𝒜 0) : A) = ((1 : (quotGradingSubmodule 𝒜 I) 0) : A ⧸ I)
    rw [show ((1 : 𝒜 0) : A) = (1 : A) from rfl, map_one]
    rfl
  map_mul' x y := Subtype.ext <| by
    show Ideal.Quotient.mk I ((x * y : 𝒜 0) : A) = _
    rw [show ((x * y : 𝒜 0) : A) = (x : A) * (y : A) from rfl, map_mul]
    rfl
  map_zero' := Subtype.ext <| by
    show Ideal.Quotient.mk I ((0 : 𝒜 0) : A) = ((0 : (quotGradingSubmodule 𝒜 I) 0) : A ⧸ I)
    rw [show ((0 : 𝒜 0) : A) = (0 : A) from rfl, map_zero]
    rfl
  map_add' x y := Subtype.ext <| by
    show Ideal.Quotient.mk I ((x + y : 𝒜 0) : A) = _
    rw [show ((x + y : 𝒜 0) : A) = (x : A) + (y : A) from rfl, map_add]
    rfl
  commutes' r := Subtype.ext <| by
    show Ideal.Quotient.mk I ((algebraMap R (𝒜 0) r : 𝒜 0) : A)
        = ((algebraMap R ((quotGradingSubmodule 𝒜 I) 0) r) : A ⧸ I)
    rfl

@[scoped simp] private lemma gradeZeroQuotAlgHom_apply_coe (x : 𝒜 0) :
    (gradeZeroQuotAlgHom 𝒜 I x : A ⧸ I) = Ideal.Quotient.mk I (x : A) := rfl

private theorem gradeZeroQuotAlgHom_surjective :
    Function.Surjective (gradeZeroQuotAlgHom 𝒜 I) := by
  rintro ⟨b, hb⟩
  obtain ⟨a, ha, rfl⟩ := (mem_quotGradingSubmodule_iff 𝒜 I).mp hb
  exact ⟨⟨a, ha⟩, rfl⟩

private theorem gradeZeroQuotAlgHom_injective_iff :
    Function.Injective (gradeZeroQuotAlgHom 𝒜 I)
      ↔ ∀ a : A, a ∈ 𝒜 0 → a ∈ I → a = 0 := by
  constructor
  · intro hinj a ha haI
    have h1 : gradeZeroQuotAlgHom 𝒜 I ⟨a, ha⟩ = gradeZeroQuotAlgHom 𝒜 I 0 := by
      apply Subtype.ext
      show Ideal.Quotient.mk I a = (gradeZeroQuotAlgHom 𝒜 I 0 : A ⧸ I)
      rw [map_zero]
      show Ideal.Quotient.mk I a = ((0 : (quotGradingSubmodule 𝒜 I) 0) : A ⧸ I)
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr haI]
      rfl
    have h2 : (⟨a, ha⟩ : 𝒜 0) = 0 := hinj h1
    simpa using congrArg Subtype.val h2
  · intro h x y hxy
    have hval : Ideal.Quotient.mk I (x : A) = Ideal.Quotient.mk I (y : A) :=
      congrArg Subtype.val hxy
    have hsub : ((x : A) - (y : A)) ∈ I := Ideal.Quotient.eq.mp hval
    have hmem : ((x : A) - (y : A)) ∈ 𝒜 0 := sub_mem x.2 y.2
    exact Subtype.ext (sub_eq_zero.mp (h _ hmem hsub))

omit [SetLike.GradedMonoid 𝒜] in

private theorem gradeZero_inf_restrictScalars_eq_bot_iff :
    𝒜 0 ⊓ Submodule.restrictScalars R I = ⊥ ↔ ∀ a : A, a ∈ 𝒜 0 → a ∈ I → a = 0 := by
  rw [Submodule.eq_bot_iff]
  constructor
  · intro h a ha haI
    exact h a (Submodule.mem_inf.mpr ⟨ha, (Submodule.restrictScalars_mem R I a).mpr haI⟩)
  · intro h a ha
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp ha
    exact h a h1 ((Submodule.restrictScalars_mem R I a).mp h2)

private noncomputable def gradeZeroQuotAlgEquiv (h : ∀ a : A, a ∈ 𝒜 0 → a ∈ I → a = 0) :
    (𝒜 0) ≃ₐ[R] ((quotGradingSubmodule 𝒜 I) 0) :=
  AlgEquiv.ofBijective (gradeZeroQuotAlgHom 𝒜 I)
    ⟨(gradeZeroQuotAlgHom_injective_iff 𝒜 I).mpr h, gradeZeroQuotAlgHom_surjective 𝒜 I⟩

@[scoped simp] private lemma gradeZeroQuotAlgEquiv_apply_coe (h : ∀ a : A, a ∈ 𝒜 0 → a ∈ I → a = 0)
    (x : 𝒜 0) :
    (gradeZeroQuotAlgEquiv 𝒜 I h x : A ⧸ I) = Ideal.Quotient.mk I (x : A) := rfl

end DegreeZeroEngine

section PolynomialDegreeZero

open MvPolynomial

private theorem mem_homogeneousSubmodule_zero_iff_exists_C {σ R : Type*} [CommSemiring R]
    {p : MvPolynomial σ R} :
    p ∈ homogeneousSubmodule σ R 0 ↔ ∃ r : R, C r = p := by
  constructor
  · intro hp
    rw [homogeneousSubmodule_zero] at hp
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hp
    exact ⟨r, by rwa [← algebraMap_eq]⟩
  · rintro ⟨r, rfl⟩
    exact (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C _ _)

variable (σ R : Type*) [CommSemiring R]

private noncomputable def homogeneousSubmoduleZeroAlgEquiv :
    R ≃ₐ[R] ((homogeneousSubmodule σ R) 0) :=
  AlgEquiv.ofBijective (Algebra.ofId R _)
    ⟨fun r s hrs => by
      have hC : (C r : MvPolynomial σ R) = C s := by
        simpa using congrArg Subtype.val hrs
      exact C_injective σ R hC,
     fun x => by
      obtain ⟨r, hr⟩ :=
        mem_homogeneousSubmodule_zero_iff_exists_C.mp (x.2 : (x : MvPolynomial σ R) ∈ _)
      exact ⟨r, Subtype.ext (by simpa using hr)⟩⟩

@[scoped simp] private lemma homogeneousSubmoduleZeroAlgEquiv_apply_coe (r : R) :
    (homogeneousSubmoduleZeroAlgEquiv σ R r : MvPolynomial σ R) = C r := rfl

end PolynomialDegreeZero

section ConstantCoeffKernel

open MvPolynomial

variable {σ R : Type*} [CommSemiring R]

private theorem constantCoeff_eq_zero_of_isHomogeneous_of_ne_zero {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsHomogeneous n) (hn : n ≠ 0) :
    constantCoeff p = 0 :=
  hp.coeff_eq_zero (by simpa using hn.symm)

private theorem span_le_ker_constantCoeff_of_forall_constantCoeff_eq_zero
    {S : Set (MvPolynomial σ R)} (h : ∀ p ∈ S, constantCoeff p = 0) :
    Ideal.span S ≤ RingHom.ker (constantCoeff : MvPolynomial σ R →+* R) :=
  Ideal.span_le.mpr fun p hp => RingHom.mem_ker.mpr (h p hp)

private theorem span_singleton_le_ker_constantCoeff {f : MvPolynomial σ R}
    (hf : constantCoeff f = 0) :
    Ideal.span {f} ≤ RingHom.ker (constantCoeff : MvPolynomial σ R →+* R) :=
  span_le_ker_constantCoeff_of_forall_constantCoeff_eq_zero
    (fun p hp => by rcases Set.mem_singleton_iff.mp hp with rfl; exact hf)

private theorem span_le_ker_constantCoeff_of_forall_isHomogeneous_pos
    {S : Set (MvPolynomial σ R)} (h : ∀ p ∈ S, ∃ n : ℕ, n ≠ 0 ∧ p.IsHomogeneous n) :
    Ideal.span S ≤ RingHom.ker (constantCoeff : MvPolynomial σ R →+* R) :=
  span_le_ker_constantCoeff_of_forall_constantCoeff_eq_zero fun p hp => by
    obtain ⟨n, hn, hhom⟩ := h p hp
    exact constantCoeff_eq_zero_of_isHomogeneous_of_ne_zero hhom hn

private theorem degreeZero_inter_trivial_of_le_ker_constantCoeff {I : Ideal (MvPolynomial σ R)}
    (hI : I ≤ RingHom.ker (constantCoeff : MvPolynomial σ R →+* R)) :
    ∀ p : MvPolynomial σ R, p ∈ homogeneousSubmodule σ R 0 → p ∈ I → p = 0 := by
  intro p hp hpI
  obtain ⟨r, hr⟩ := mem_homogeneousSubmodule_zero_iff_exists_C.mp hp
  have h0 : constantCoeff p = 0 := RingHom.mem_ker.mp (hI hpI)
  rw [← hr, constantCoeff_C] at h0
  rw [← hr, h0, map_zero]

end ConstantCoeffKernel

section DegreeZeroIdentification

open MvPolynomial

variable {σ R : Type*} [CommRing R]
variable (I : Ideal (MvPolynomial σ R))

private noncomputable def quotGradingSubmoduleDegreeZeroAlgEquiv
    (hI : I ≤ RingHom.ker (constantCoeff : MvPolynomial σ R →+* R)) :
    R ≃ₐ[R] ((quotGradingSubmodule (homogeneousSubmodule σ R) I) 0) :=
  (homogeneousSubmoduleZeroAlgEquiv σ R).trans
    (gradeZeroQuotAlgEquiv (homogeneousSubmodule σ R) I
      (degreeZero_inter_trivial_of_le_ker_constantCoeff hI))

@[scoped simp] private lemma quotGradingSubmoduleDegreeZeroAlgEquiv_apply_coe
    (hI : I ≤ RingHom.ker (constantCoeff : MvPolynomial σ R →+* R)) (r : R) :
    (quotGradingSubmoduleDegreeZeroAlgEquiv I hI r : MvPolynomial σ R ⧸ I)
      = Ideal.Quotient.mk I (C r) := rfl

private lemma quotGradingSubmodule_degreeZero_algebraMap_coe (r : R) :
    ((algebraMap R ((quotGradingSubmodule (homogeneousSubmodule σ R) I) 0) r :
        (quotGradingSubmodule (homogeneousSubmodule σ R) I) 0) : MvPolynomial σ R ⧸ I)
      = Ideal.Quotient.mk I (C r) := rfl

private lemma coe_quotGradingSubmoduleDegreeZeroAlgEquiv_eq_algebraMap
    (hI : I ≤ RingHom.ker (constantCoeff : MvPolynomial σ R →+* R)) :
    ⇑(quotGradingSubmoduleDegreeZeroAlgEquiv I hI)
      = ⇑(algebraMap R ((quotGradingSubmodule (homogeneousSubmodule σ R) I) 0)) :=
  funext fun _ => Subtype.ext rfl

private theorem quotGradingSubmodule_degreeZero_algebraMap_surjective :
    Function.Surjective
      (algebraMap R ((quotGradingSubmodule (homogeneousSubmodule σ R) I) 0)) := by
  rintro ⟨b, hb⟩
  obtain ⟨p, hp, rfl⟩ := (mem_quotGradingSubmodule_iff (homogeneousSubmodule σ R) I).mp hb
  obtain ⟨r, rfl⟩ := mem_homogeneousSubmodule_zero_iff_exists_C.mp hp
  exact ⟨r, Subtype.ext rfl⟩

private theorem quotGradingSubmodule_degreeZero_algebraMap_injective
    (hI : I ≤ RingHom.ker (constantCoeff : MvPolynomial σ R →+* R)) :
    Function.Injective
      (algebraMap R ((quotGradingSubmodule (homogeneousSubmodule σ R) I) 0)) := by
  intro r s hrs
  have hval : Ideal.Quotient.mk I (C r) = Ideal.Quotient.mk I (C s) :=
    congrArg Subtype.val hrs
  have hsub : (C r - C s : MvPolynomial σ R) ∈ I := Ideal.Quotient.eq.mp hval
  rw [← map_sub] at hsub
  have h0 : constantCoeff (C (r - s) : MvPolynomial σ R) = 0 := RingHom.mem_ker.mp (hI hsub)
  rw [constantCoeff_C] at h0
  exact sub_eq_zero.mp h0

private theorem quotGradingSubmodule_degreeZero_algebraMap_bijective
    (hI : I ≤ RingHom.ker (constantCoeff : MvPolynomial σ R →+* R)) :
    Function.Bijective
      (algebraMap R ((quotGradingSubmodule (homogeneousSubmodule σ R) I) 0)) :=
  ⟨quotGradingSubmodule_degreeZero_algebraMap_injective I hI,
   quotGradingSubmodule_degreeZero_algebraMap_surjective I⟩

end DegreeZeroIdentification

end HomogeneousIdealQuotientGrading
p2m_reactivate "P2MW.S_WeierstrassProjModel_projModelStrCR_isProper.HomogeneousIdealQuotientGrading"

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
p2m_open "HomogeneousIdealQuotientGrading P2MW.S_WeierstrassProjModel_projModelStrCR_isProper.HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime"

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR ProjModelRingCR projModelGradingCR projModelCR projModelStrCR"
p2m_open "WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type*} [CommRing R]

@[reducible] private def projModel_gradedAlgebraCR (V : WeierstrassCurve.Projective R) :
    GradedAlgebra (projModelGradingCR V) := inferInstance

@[reducible] private def projModel_gradedRingCR (V : WeierstrassCurve.Projective R) :
    GradedRing (projModelGradingCR V) := inferInstance

private theorem projModel_finiteType_degreeZeroCR (V : WeierstrassCurve.Projective R) :
    Algebra.FiniteType ((projModelGradingCR V) 0) (ProjModelRingCR V) := inferInstance

private theorem projModelIdeal_le_ker_constantCoeffCR (V : WeierstrassCurve.Projective R) :
    (projModelHomogeneousIdealCR V).toIdeal
      ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin 3) R →+* R) :=
  span_le_ker_constantCoeff_of_forall_isHomogeneous_pos fun p hp => by
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact ⟨3, by decide, isHomogeneous_polynomial V⟩

private def projModelDegreeZeroAlgEquivCR (V : WeierstrassCurve.Projective R) :
    R ≃ₐ[R] ((projModelGradingCR V) 0) :=
  quotGradingSubmoduleDegreeZeroAlgEquiv (projModelHomogeneousIdealCR V).toIdeal
    (projModelIdeal_le_ker_constantCoeffCR V)

private theorem projModel_degreeZero_algebraMap_bijectiveCR (V : WeierstrassCurve.Projective R) :
    Function.Bijective (algebraMap R ((projModelGradingCR V) 0)) :=
  quotGradingSubmodule_degreeZero_algebraMap_bijective (projModelHomogeneousIdealCR V).toIdeal
    (projModelIdeal_le_ker_constantCoeffCR V)

private def projModelDegreeZeroRingEquivCR (V : WeierstrassCurve.Projective R) :
    R ≃+* ((projModelGradingCR V) 0) :=
  RingEquiv.ofBijective (algebraMap R ((projModelGradingCR V) 0))
    (projModel_degreeZero_algebraMap_bijectiveCR V)

private def projModelSpecDegreeZeroIsoCR (V : WeierstrassCurve.Projective R) :
    Spec (CommRingCat.of ((projModelGradingCR V) 0)) ≅ Spec (CommRingCat.of R) where
  hom := Spec.map (CommRingCat.ofHom (algebraMap R ((projModelGradingCR V) 0)))
  inv := Spec.map (CommRingCat.ofHom
    ((projModelDegreeZeroRingEquivCR V).symm : ((projModelGradingCR V) 0) →+* R))
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show (algebraMap R ((projModelGradingCR V) 0)).comp
          ((projModelDegreeZeroRingEquivCR V).symm : ((projModelGradingCR V) 0) →+* R)
        = RingHom.id ((projModelGradingCR V) 0) from
        RingHom.ext fun x => (projModelDegreeZeroRingEquivCR V).apply_symm_apply x,
      CommRingCat.ofHom_id, Spec.map_id]
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show ((projModelDegreeZeroRingEquivCR V).symm : ((projModelGradingCR V) 0) →+* R).comp
          (algebraMap R ((projModelGradingCR V) 0))
        = RingHom.id R from
        RingHom.ext fun x => (projModelDegreeZeroRingEquivCR V).symm_apply_apply x,
      CommRingCat.ofHom_id, Spec.map_id]

private scoped instance projModel_isIso_spec_mapCR (V : WeierstrassCurve.Projective R) :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap R ((projModelGradingCR V) 0)))) :=
  inferInstanceAs (IsIso (projModelSpecDegreeZeroIsoCR V).hom)

private theorem projModelStrCR_eq_comp_iso_hom (V : WeierstrassCurve.Projective R) :
    projModelStrCR V
      = Proj.toSpecZero (projModelGradingCR V) ≫ (projModelSpecDegreeZeroIsoCR V).hom := rfl

private scoped instance isProper_projModelStrCR (V : WeierstrassCurve.Projective R) :
    IsProper (projModelStrCR V) := by
  show IsProper (Proj.toSpecZero (projModelGradingCR V) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R ((projModelGradingCR V) 0))))
  infer_instance

private theorem isSeparated_projModelStrCR (V : WeierstrassCurve.Projective R) :
    IsSeparated (projModelStrCR V) := inferInstance

private theorem universallyClosed_projModelStrCR (V : WeierstrassCurve.Projective R) :
    UniversallyClosed (projModelStrCR V) := inferInstance

private theorem locallyOfFiniteType_projModelStrCR (V : WeierstrassCurve.Projective R) :
    LocallyOfFiniteType (projModelStrCR V) := inferInstance

private theorem quasiCompact_projModelStrCR (V : WeierstrassCurve.Projective R) :
    QuasiCompact (projModelStrCR V) := inferInstance

end WeierstrassProjModel
p2m_reactivate "P2MW.S_WeierstrassProjModel_projModelStrCR_isProper.HomogeneousIdealQuotientGrading P2MW.S_WeierstrassProjModel_projModelStrCR_isProper.WeierstrassProjModel"

end
p2m_reactivate "P2MW.S_WeierstrassProjModel_projModelStrCR_isProper.HomogeneousIdealQuotientGrading P2MW.S_WeierstrassProjModel_projModelStrCR_isProper.WeierstrassProjModel"

theorem solution {R : Type*} [CommRing R] (V : WeierstrassCurve.Projective R) :
    AlgebraicGeometry.IsProper (WeierstrassProjModel.projModelStrCR V) :=
  WeierstrassProjModel.isProper_projModelStrCR V

end S_WeierstrassProjModel_projModelStrCR_isProper
end P2MW
export P2MW.S_WeierstrassProjModel_projModelStrCR_isProper (solution)
