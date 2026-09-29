-- Prove2me | solution 1 for WeierstrassProjModel.RelativeGroupLaw.exists_isCommutative_one_eq_zeroSect_of_isCommutative
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/3365b0f4-710a-5f87-ba90-984450e79d02

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_RelativeGroupLaw_exists_isCommutative_one_eq_zeroSect_of_isCommutative

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u

theorem solution
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)
    (G₁ : RelativeGroupLaw R (projModelStrCR V))
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (x y : SchemeHomOver t (projModelStrCR V)), G₁.mul t x y = G₁.mul t y x) :
    ∃ G₀ : RelativeGroupLaw R (projModelStrCR V),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (x y : SchemeHomOver t (projModelStrCR V)), G₀.mul t x y = G₀.mul t y x)
      ∧ (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
          (G₀.one t).1 = t ≫ (kwZeroSect R V.toAffine).1) := by

  set zs := kwZeroSect R V.toAffine with hzs
  let e₀ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      SchemeHomOver t (projModelStrCR V) :=
    fun {T} t => ⟨t ≫ zs.1, by rw [Category.assoc, zs.2, Category.comp_id]⟩

  have he₀_nat : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t'),
      schemeHomOverComp ψ hψ (e₀ t) = e₀ t' := by
    intro T T' t t' ψ hψ
    apply Subtype.ext
    show ψ ≫ (t ≫ zs.1) = t' ≫ zs.1
    rw [← Category.assoc, hψ]

  have hinv_nat : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
      (z : SchemeHomOver t (projModelStrCR V)),
      schemeHomOverComp ψ hψ (G₁.inv t z) = G₁.inv t' (schemeHomOverComp ψ hψ z) := by
    intro T T' t t' ψ hψ z
    letI := G₁.pointGroup t'
    have h : G₁.mul t' (schemeHomOverComp ψ hψ (G₁.inv t z)) (schemeHomOverComp ψ hψ z)
        = G₁.one t' := by
      rw [← G₁.mul_natural t t' ψ hψ, G₁.inv_mul_cancel]
      exact G₁.one_natural t t' ψ hψ
    exact eq_inv_of_mul_eq_one_left h
  refine ⟨{
    mul := fun {T} t P Q => G₁.mul t (G₁.mul t P Q) (G₁.inv t (e₀ t))
    one := fun {T} t => e₀ t
    inv := fun {T} t P => G₁.mul t (G₁.mul t (G₁.inv t P) (e₀ t)) (e₀ t)
    mul_assoc := ?_
    one_mul := ?_
    mul_one := ?_
    inv_mul_cancel := ?_
    mul_natural := ?_ }, ?_, fun {T} t => rfl⟩
  · intro T t x y z
    letI : CommGroup (SchemeHomOver t (projModelStrCR V)) :=
      { G₁.pointGroup t with mul_comm := hcomm t }
    show (x * y * (e₀ t)⁻¹ * z) * (e₀ t)⁻¹ = (x * (y * z * (e₀ t)⁻¹)) * (e₀ t)⁻¹
    rw [mul_right_comm (x * y) (e₀ t)⁻¹ z, ← mul_assoc x (y * z) (e₀ t)⁻¹, ← mul_assoc x y z]
  · intro T t x
    letI : CommGroup (SchemeHomOver t (projModelStrCR V)) :=
      { G₁.pointGroup t with mul_comm := hcomm t }
    show e₀ t * x * (e₀ t)⁻¹ = x
    rw [mul_comm (e₀ t) x, mul_inv_cancel_right]
  · intro T t x
    letI : CommGroup (SchemeHomOver t (projModelStrCR V)) :=
      { G₁.pointGroup t with mul_comm := hcomm t }
    show x * e₀ t * (e₀ t)⁻¹ = x
    exact mul_inv_cancel_right x (e₀ t)
  · intro T t x
    letI : CommGroup (SchemeHomOver t (projModelStrCR V)) :=
      { G₁.pointGroup t with mul_comm := hcomm t }
    show (x⁻¹ * e₀ t * e₀ t * x) * (e₀ t)⁻¹ = e₀ t
    rw [mul_right_comm (x⁻¹ * e₀ t * e₀ t) x (e₀ t)⁻¹, mul_inv_cancel_right,
      mul_right_comm x⁻¹ (e₀ t) x, inv_mul_cancel, one_mul]
  · intro T T' t t' ψ hψ x y
    simp only [G₁.mul_natural t t' ψ hψ, hinv_nat t t' ψ hψ, he₀_nat t t' ψ hψ]
  · intro T t x y
    letI : CommGroup (SchemeHomOver t (projModelStrCR V)) :=
      { G₁.pointGroup t with mul_comm := hcomm t }
    show x * y * (e₀ t)⁻¹ = y * x * (e₀ t)⁻¹
    rw [mul_comm x y]

end S_WeierstrassProjModel_RelativeGroupLaw_exists_isCommutative_one_eq_zeroSect_of_isCommutative
end P2MW
export P2MW.S_WeierstrassProjModel_RelativeGroupLaw_exists_isCommutative_one_eq_zeroSect_of_isCommutative (solution)
