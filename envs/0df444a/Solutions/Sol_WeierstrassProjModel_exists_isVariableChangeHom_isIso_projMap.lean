-- Prove2me | solution 1 for WeierstrassProjModel.exists_isVariableChangeHom_isIso_projMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/4986af67-f60d-571a-94b8-2060c1d50089

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap

set_option autoImplicit false

universe u

p2m_open "AlgebraicGeometry P2MW.S_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap.AlgebraicGeometry CategoryTheory WeierstrassProjModel P2MW.S_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap.WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Proj.awayι_toSpecZero_assoc Proj.awayι_toSpecZero Proj.awayι_comp_map_assoc Scheme.AffineOpenCover.openCover_f Spec Spec.map Scheme Proj.toSpecZero Proj.map_id Proj Proj.mapAffineOpenCover Scheme.AffineOpenCover.openCover_X Proj.mapAffineOpenCover_f Proj.map Scheme.AffineOpenCover Proj.map_comp"
namespace Proj
p2m_export "AlgebraicGeometry.Proj" "awayι_toSpecZero_assoc awayι_toSpecZero awayι_comp_map_assoc toSpecZero map_id mapAffineOpenCover ext mapAffineOpenCover_f map map_comp"
p2m_open "AlgebraicGeometry.Proj AlgebraicGeometry"

open HomogeneousLocalization

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)

lemma awayMap_comp_fromZeroRingHom (s : A) :
    (Away.map f s).comp (fromZeroRingHom 𝒜 (.powers s)) =
      (fromZeroRingHom ℬ (.powers (f s))).comp f.gradedZeroRingHom := by
  ext a
  simp [fromZeroRingHom, Away.map, HomogeneousLocalization.map_mk, GradedRingHom.gradedZeroRingHom]

set_option backward.isDefEq.respectTransparency false in

theorem map_comp_toSpecZero :
    Proj.map f hf ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom) := by
  refine (Proj.mapAffineOpenCover f hf).openCover.hom_ext _ _ fun s ↦ ?_
  simp only [Scheme.AffineOpenCover.openCover_X, Scheme.AffineOpenCover.openCover_f,
    Proj.mapAffineOpenCover_f]
  rw [Proj.awayι_comp_map_assoc _ _ _ _ s.2.2, Proj.awayι_toSpecZero, Proj.awayι_toSpecZero_assoc,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    awayMap_comp_fromZeroRingHom]

end AlgebraicGeometry.Proj

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "projModelHomogeneousIdealCR projModelHomogeneousIdealCR_toIdeal ProjModelRingCR projModelGradingCR projModelStrCR"
namespace VCIso
p2m_open "WeierstrassProjModel"

open MvPolynomial

lemma key_identity {S : Type*} [CommRing S] (u v a₁ a₂ a₃ a₄ a₆ r s t X Y Z : S)
    (h : u * v = 1) :
    (u ^ 3 * Y + u ^ 2 * s * X + t * Z) ^ 2 * Z
        + a₁ * (u ^ 2 * X + r * Z) * (u ^ 3 * Y + u ^ 2 * s * X + t * Z) * Z
        + a₃ * (u ^ 3 * Y + u ^ 2 * s * X + t * Z) * Z ^ 2
      - ((u ^ 2 * X + r * Z) ^ 3 + a₂ * (u ^ 2 * X + r * Z) ^ 2 * Z
          + a₄ * (u ^ 2 * X + r * Z) * Z ^ 2 + a₆ * Z ^ 3)
    = u ^ 6 * (Y ^ 2 * Z + v * (a₁ + 2 * s) * X * Y * Z
        + v ^ 3 * (a₃ + r * a₁ + 2 * t) * Y * Z ^ 2
      - (X ^ 3 + v ^ 2 * (a₂ - s * a₁ + 3 * r - s ^ 2) * X ^ 2 * Z
          + v ^ 4 * (a₄ - s * a₃ + 2 * r * a₂ - (t + r * s) * a₁ + 3 * r ^ 2 - 2 * s * t) * X * Z ^ 2
          + v ^ 6 * (a₆ + r * a₄ + r ^ 2 * a₂ + r ^ 3 - t * a₃ - t ^ 2 - r * t * a₁) * Z ^ 3)) := by
  have e : ∀ n k : ℕ, u ^ (n + k) * v ^ k = u ^ n := fun n k ↦ by
    rw [pow_add, mul_assoc, ← mul_pow, h, one_pow, mul_one]
  have e1 : u ^ 6 * v = u ^ 5 := by simpa using e 5 1
  have e2 : u ^ 6 * v ^ 2 = u ^ 4 := e 4 2
  have e3 : u ^ 6 * v ^ 3 = u ^ 3 := e 3 3
  have e4 : u ^ 6 * v ^ 4 = u ^ 2 := e 2 4
  have e6 : u ^ 6 * v ^ 6 = 1 := by simpa using e 0 6
  calc _ = u ^ 6 * Y ^ 2 * Z + u ^ 5 * (a₁ + 2 * s) * X * Y * Z
        + u ^ 3 * (a₃ + r * a₁ + 2 * t) * Y * Z ^ 2
      - (u ^ 6 * X ^ 3 + u ^ 4 * (a₂ - s * a₁ + 3 * r - s ^ 2) * X ^ 2 * Z
          + u ^ 2 * (a₄ - s * a₃ + 2 * r * a₂ - (t + r * s) * a₁ + 3 * r ^ 2 - 2 * s * t) * X * Z ^ 2
          + (a₆ + r * a₄ + r ^ 2 * a₂ + r ^ 3 - t * a₃ - t ^ 2 - r * t * a₁) * Z ^ 3) := by ring
    _ = (u ^ 6) * Y ^ 2 * Z + (u ^ 6 * v) * (a₁ + 2 * s) * X * Y * Z
        + (u ^ 6 * v ^ 3) * (a₃ + r * a₁ + 2 * t) * Y * Z ^ 2
      - ((u ^ 6) * X ^ 3 + (u ^ 6 * v ^ 2) * (a₂ - s * a₁ + 3 * r - s ^ 2) * X ^ 2 * Z
          + (u ^ 6 * v ^ 4) * (a₄ - s * a₃ + 2 * r * a₂ - (t + r * s) * a₁ + 3 * r ^ 2 - 2 * s * t) * X * Z ^ 2
          + (u ^ 6 * v ^ 6) * (a₆ + r * a₄ + r ^ 2 * a₂ + r ^ 3 - t * a₃ - t ^ 2 - r * t * a₁) * Z ^ 3) := by
      rw [e1, e2, e3, e4, e6, one_mul]
    _ = _ := by ring

variable {T : Type u} [CommRing T]

noncomputable def vcSubst (vc : WeierstrassCurve.VariableChange T) : Fin 3 → MvPolynomial (Fin 3) T :=
  ![C ((vc.u : T) ^ 2) * X 0 + C vc.r * X 2,
    C ((vc.u : T) ^ 3) * X 1 + C ((vc.u : T) ^ 2 * vc.s) * X 0 + C vc.t * X 2,
    X 2]

@[scoped simp] lemma inv_u (vc : WeierstrassCurve.VariableChange T) : vc⁻¹.u = vc.u⁻¹ := rfl
@[scoped simp] lemma inv_r (vc : WeierstrassCurve.VariableChange T) : vc⁻¹.r = -vc.r * (vc.u⁻¹ : Tˣ) ^ 2 := rfl
@[scoped simp] lemma inv_s (vc : WeierstrassCurve.VariableChange T) : vc⁻¹.s = -vc.s * (vc.u⁻¹ : Tˣ) := rfl
@[scoped simp] lemma inv_t (vc : WeierstrassCurve.VariableChange T) :
    vc⁻¹.t = (vc.r * vc.s - vc.t) * (vc.u⁻¹ : Tˣ) ^ 3 := rfl

@[scoped simp] lemma vcSubst_zero (vc : WeierstrassCurve.VariableChange T) :
    vcSubst vc 0 = C ((vc.u : T) ^ 2) * X 0 + C vc.r * X 2 := rfl
@[scoped simp] lemma vcSubst_one (vc : WeierstrassCurve.VariableChange T) :
    vcSubst vc 1 = C ((vc.u : T) ^ 3) * X 1 + C ((vc.u : T) ^ 2 * vc.s) * X 0 + C vc.t * X 2 := rfl
@[scoped simp] lemma vcSubst_two (vc : WeierstrassCurve.VariableChange T) : vcSubst vc 2 = X 2 := rfl

lemma vcSubst_isHomogeneous (vc : WeierstrassCurve.VariableChange T) (i : Fin 3) :
    (vcSubst vc i).IsHomogeneous 1 := by
  fin_cases i
  · exact ((isHomogeneous_X T 0).C_mul _).add ((isHomogeneous_X T 2).C_mul _)
  · exact (((isHomogeneous_X T 1).C_mul _).add ((isHomogeneous_X T 0).C_mul _)).add
      ((isHomogeneous_X T 2).C_mul _)
  · exact isHomogeneous_X T 2

lemma aeval_vcSubst_polynomial (vc : WeierstrassCurve.VariableChange T)
    (V : WeierstrassCurve.Projective T) :
    aeval (vcSubst vc) V.polynomial = C ((vc.u : T) ^ 6) * (vc • V).polynomial := by
  have h : (C (vc.u : T) : MvPolynomial (Fin 3) T) * C ((vc.u⁻¹ : Tˣ) : T) = 1 := by
    rw [← C_mul, Units.mul_inv, C_1]
  simp only [WeierstrassCurve.Projective.polynomial, map_add, map_sub, map_mul, map_pow, aeval_X,
    aeval_C, algebraMap_eq, vcSubst_zero, vcSubst_one, vcSubst_two,
    WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆, map_ofNat]
  linear_combination key_identity (C (vc.u : T)) (C ((vc.u⁻¹ : Tˣ) : T)) (C V.a₁) (C V.a₂) (C V.a₃)
    (C V.a₄) (C V.a₆) (C vc.r) (C vc.s) (C vc.t) (X 0) (X 1) (X 2) h

lemma aeval_vcSubst_inv_vcSubst_zero (vc : WeierstrassCurve.VariableChange T) :
    aeval (vcSubst vc⁻¹) (vcSubst vc 0) = X 0 := by
  have h : (C (vc.u : T) : MvPolynomial (Fin 3) T) * C ((vc.u⁻¹ : Tˣ) : T) = 1 := by
    rw [← C_mul, Units.mul_inv, C_1]
  simp only [vcSubst_zero, map_add, map_mul, map_pow, aeval_X, aeval_C, algebraMap_eq,
    vcSubst_two, inv_u, inv_r, map_neg]
  linear_combination ((C (vc.u : T)) * C ((vc.u⁻¹ : Tˣ) : T) + 1) * (X 0 - C vc.r * X 2) * h

lemma aeval_vcSubst_inv_vcSubst_one (vc : WeierstrassCurve.VariableChange T) :
    aeval (vcSubst vc⁻¹) (vcSubst vc 1) = X 1 := by
  have h : (C (vc.u : T) : MvPolynomial (Fin 3) T) * C ((vc.u⁻¹ : Tˣ) : T) = 1 := by
    rw [← C_mul, Units.mul_inv, C_1]
  simp only [vcSubst_one, vcSubst_zero, map_add, map_mul, map_pow, map_sub, aeval_X, aeval_C,
    algebraMap_eq, vcSubst_two, inv_u, inv_r, inv_s, inv_t, map_neg]
  linear_combination (((C (vc.u : T)) * C ((vc.u⁻¹ : Tˣ) : T)) ^ 2
      + (C (vc.u : T)) * C ((vc.u⁻¹ : Tˣ) : T) + 1)
      * (X 1 - C vc.s * X 0 + (C vc.r * C vc.s - C vc.t) * X 2) * h
    + ((C (vc.u : T)) * C ((vc.u⁻¹ : Tˣ) : T) + 1) * (C vc.s * X 0 - C vc.r * C vc.s * X 2) * h

lemma aeval_vcSubst_inv_vcSubst (vc : WeierstrassCurve.VariableChange T) (i : Fin 3) :
    aeval (vcSubst vc⁻¹) (vcSubst vc i) = X i := by
  fin_cases i
  · exact aeval_vcSubst_inv_vcSubst_zero vc
  · exact aeval_vcSubst_inv_vcSubst_one vc
  · simp [vcSubst_two]

open HomogeneousIdealQuotientGrading

section Subst

variable (g : Fin 3 → MvPolynomial (Fin 3) T) (hg : ∀ i, (g i).IsHomogeneous 1)

include hg in
lemma aeval_mem_homogeneousSubmodule {n : ℕ} {p : MvPolynomial (Fin 3) T}
    (hp : p ∈ homogeneousSubmodule (Fin 3) T n) :
    aeval g p ∈ homogeneousSubmodule (Fin 3) T n := by
  rw [mem_homogeneousSubmodule] at hp ⊢
  simpa using hp.aeval g hg

noncomputable def substHom (V V' : WeierstrassCurve.Projective T)
    (hV : aeval g V.polynomial ∈ Ideal.span {V'.polynomial}) :
    projModelGradingCR V →+*ᵍ projModelGradingCR V' where
  __ := Ideal.Quotient.lift (projModelHomogeneousIdealCR V).toIdeal
      ((Ideal.Quotient.mk (projModelHomogeneousIdealCR V').toIdeal).comp (aeval g).toRingHom)
      (by
        intro a ha
        rw [projModelHomogeneousIdealCR_toIdeal, Ideal.mem_span_singleton] at ha
        obtain ⟨c, rfl⟩ := ha
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, projModelHomogeneousIdealCR_toIdeal]
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul]
        exact Ideal.mul_mem_right _ _ hV)
  map_mem := by
    intro i x hx
    obtain ⟨a, ha, rfl⟩ := (mem_quotGradingSubmodule_iff _ _).mp hx
    rw [Ideal.Quotient.lift_mk, RingHom.comp_apply]
    exact mk_mem_quotGradingSubmodule _ _ (aeval_mem_homogeneousSubmodule g hg ha)

@[scoped simp] lemma substHom_mk (V V' : WeierstrassCurve.Projective T)
    (hV : aeval g V.polynomial ∈ Ideal.span {V'.polynomial}) (p : MvPolynomial (Fin 3) T) :
    substHom g hg V V' hV (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (aeval g p) := rfl

lemma substHom_comp_substHom (g' : Fin 3 → MvPolynomial (Fin 3) T) (hg' : ∀ i, (g' i).IsHomogeneous 1)
    (V V' : WeierstrassCurve.Projective T)
    (hV : aeval g V.polynomial ∈ Ideal.span {V'.polynomial})
    (hV' : aeval g' V'.polynomial ∈ Ideal.span {V.polynomial})
    (hcomp : ∀ i, aeval g' (g i) = X i) :
    (substHom g' hg' V' V hV').comp (substHom g hg V V' hV) = GradedRingHom.id _ := by
  have key : (aeval g').comp (aeval g) = AlgHom.id T (MvPolynomial (Fin 3) T) :=
    MvPolynomial.algHom_ext fun i ↦ by
      rw [AlgHom.comp_apply, aeval_X, AlgHom.id_apply]
      exact hcomp i
  refine GradedRingHom.ext fun x ↦ ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [GradedRingHom.comp_apply, substHom_mk, substHom_mk, GradedRingHom.id_apply, ← AlgHom.comp_apply,
    key, AlgHom.id_apply]

end Subst

section Inverse

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

lemma irrelevant_le_map_of_comp_eq_id {φ : 𝒜 →+*ᵍ ℬ} {ψ : ℬ →+*ᵍ 𝒜}
    (h : φ.comp ψ = GradedRingHom.id ℬ) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ :=
  (HomogeneousIdeal.irrelevant_le _).mpr fun i hi x hx ↦ by
    have hx' : x = φ (ψ x) := (GradedRingHom.congr_fun h x).symm
    rw [hx']
    exact Ideal.mem_map_of_mem _
      (HomogeneousIdeal.mem_irrelevant_of_mem _ hi (Graded.map_mem ψ hx))

lemma isIso_map_of_comp_eq_id {φ : 𝒜 →+*ᵍ ℬ} {ψ : ℬ →+*ᵍ 𝒜}
    (h₁ : φ.comp ψ = GradedRingHom.id ℬ) (h₂ : ψ.comp φ = GradedRingHom.id 𝒜)
    (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)
    (hψ : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant ℬ).map ψ) :
    IsIso (Proj.map φ hφ) := by
  have H : ∀ {C' : Type u} {ω : Type u} [CommRing C'] [SetLike ω C'] [AddSubgroupClass ω C']
      {𝒞 : ℕ → ω} [GradedRing 𝒞] (χ : 𝒞 →+*ᵍ 𝒞)
      (hχ : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant 𝒞).map χ),
      χ = GradedRingHom.id 𝒞 → Proj.map χ hχ = 𝟙 _ := by
    intro C' ω _ _ _ 𝒞 _ χ hχ e
    subst e
    exact Proj.map_id
  refine ⟨⟨Proj.map ψ hψ, ?_, ?_⟩⟩
  · rw [← Proj.map_comp ψ φ hψ hφ]
    exact H _ _ h₁
  · rw [← Proj.map_comp φ ψ hφ hψ]
    exact H _ _ h₂

end Inverse

noncomputable def vcHom (vc : WeierstrassCurve.VariableChange T) (V : WeierstrassCurve.Projective T) :
    projModelGradingCR V →+*ᵍ projModelGradingCR (vc • V) :=
  substHom (vcSubst vc) (vcSubst_isHomogeneous vc) V (vc • V)
    (by
      rw [aeval_vcSubst_polynomial, Ideal.mem_span_singleton]
      exact Dvd.intro_left _ rfl)

noncomputable def vcInvHom (vc : WeierstrassCurve.VariableChange T) (V : WeierstrassCurve.Projective T) :
    projModelGradingCR (vc • V) →+*ᵍ projModelGradingCR V :=
  substHom (vcSubst vc⁻¹) (vcSubst_isHomogeneous vc⁻¹) (vc • V) V
    (by
      rw [aeval_vcSubst_polynomial, inv_smul_smul, Ideal.mem_span_singleton]
      exact Dvd.intro_left _ rfl)

lemma vcInvHom_comp_vcHom (vc : WeierstrassCurve.VariableChange T) (V : WeierstrassCurve.Projective T) :
    (vcInvHom vc V).comp (vcHom vc V) = GradedRingHom.id _ :=
  substHom_comp_substHom _ _ _ _ _ _ _ _ (aeval_vcSubst_inv_vcSubst vc)

lemma vcHom_comp_vcInvHom (vc : WeierstrassCurve.VariableChange T) (V : WeierstrassCurve.Projective T) :
    (vcHom vc V).comp (vcInvHom vc V) = GradedRingHom.id _ :=
  substHom_comp_substHom _ _ _ _ _ _ _ _ (by simpa only [inv_inv] using aeval_vcSubst_inv_vcSubst vc⁻¹)

lemma irrelevant_le_map_vcHom (vc : WeierstrassCurve.VariableChange T) (V : WeierstrassCurve.Projective T) :
    HomogeneousIdeal.irrelevant (projModelGradingCR (vc • V)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR V)).map (vcHom vc V) :=
  irrelevant_le_map_of_comp_eq_id (vcHom_comp_vcInvHom vc V)

lemma irrelevant_le_map_vcInvHom (vc : WeierstrassCurve.VariableChange T) (V : WeierstrassCurve.Projective T) :
    HomogeneousIdeal.irrelevant (projModelGradingCR V) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR (vc • V))).map (vcInvHom vc V) :=
  irrelevant_le_map_of_comp_eq_id (vcInvHom_comp_vcHom vc V)

lemma isVariableChangeHom_vcHom (vc : WeierstrassCurve.VariableChange T)
    (V : WeierstrassCurve.Projective T) : IsVariableChangeHom V vc (vcHom vc V) := by
  refine ⟨fun a ↦ ?_, ?_, ?_, ?_⟩
  · change Ideal.Quotient.mk _ (aeval (vcSubst vc) (MvPolynomial.C a)) = _
    rw [aeval_C, algebraMap_eq]
  · change Ideal.Quotient.mk _ (aeval (vcSubst vc) (X 0)) = _
    rw [aeval_X, vcSubst_zero]
  · change Ideal.Quotient.mk _ (aeval (vcSubst vc) (X 1)) = _
    rw [aeval_X, vcSubst_one]
  · change Ideal.Quotient.mk _ (aeval (vcSubst vc) (X 2)) = _
    rw [aeval_X, vcSubst_two]

lemma isIso_map_vcHom (vc : WeierstrassCurve.VariableChange T) (V : WeierstrassCurve.Projective T) :
    IsIso (Proj.map (vcHom vc V) (irrelevant_le_map_vcHom vc V)) :=
  isIso_map_of_comp_eq_id (vcHom_comp_vcInvHom vc V) (vcInvHom_comp_vcHom vc V) _
    (irrelevant_le_map_vcInvHom vc V)

lemma map_vcHom_comp_projModelStrCR (vc : WeierstrassCurve.VariableChange T)
    (V : WeierstrassCurve.Projective T) :
    Proj.map (vcHom vc V) (irrelevant_le_map_vcHom vc V) ≫ projModelStrCR V =
      projModelStrCR (vc • V) := by
  have e1 : ∀ a, ((vcHom vc V).gradedZeroRingHom a : ProjModelRingCR (vc • V)) =
      vcHom vc V (a : ProjModelRingCR V) := fun _ ↦ rfl
  have key : (vcHom vc V).gradedZeroRingHom.comp (algebraMap T (projModelGradingCR V 0)) =
      algebraMap T (projModelGradingCR (vc • V) 0) := by
    refine RingHom.ext fun a ↦ Subtype.ext ?_
    rw [RingHom.comp_apply, e1, SetLike.GradeZero.coe_algebraMap, SetLike.GradeZero.coe_algebraMap,
      ← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]
    exact (isVariableChangeHom_vcHom vc V).1 a
  rw [projModelStrCR, projModelStrCR, ← Category.assoc, Proj.map_comp_toSpecZero, Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, key]

end WeierstrassProjModel.VCIso
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap.WeierstrassProjModel P2MW.S_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap.WeierstrassProjModel.VCIso"
p2m_reactivate "P2MW.S_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap.WeierstrassProjModel"

open WeierstrassProjModel.VCIso in
theorem solution
    {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T) :
    ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
      (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤
        (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
      IsVariableChangeHom W C φ ∧ IsIso (Proj.map φ hφ) ∧
      Proj.map φ hφ ≫ projModelStrCR W = projModelStrCR (C • W) :=
  ⟨vcHom C W, irrelevant_le_map_vcHom C W, isVariableChangeHom_vcHom C W, isIso_map_vcHom C W,
    map_vcHom_comp_projModelStrCR C W⟩

end S_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap
end P2MW
export P2MW.S_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap (solution)
