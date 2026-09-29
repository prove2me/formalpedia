-- Prove2me | solution 1 for WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/6f4198e7-2e3d-58ec-a8d3-9513136cce43

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_WeierstrassProjModel_eq_snd_comp_of_comp_eq_const_of_isElliptic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_of_isElliptic
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

set_option autoImplicit false

universe u

p2m_open "AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_of_isElliptic.WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "schemeHomOverComp RelativeGroupLaw projModelCR projModelStrCR eq_snd_comp_of_comp_eq_const_of_isElliptic"
namespace RelativeGroupLaw
p2m_export "WeierstrassProjModel.RelativeGroupLaw" "pointGroup one_natural mul_one one_mul inv mul mul_natural one"
namespace RigidUnit
p2m_open "WeierstrassProjModel.RelativeGroupLaw WeierstrassProjModel"

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

noncomputable def compHom (G : RelativeGroupLaw R f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    letI := G.pointGroup t
    letI := G.pointGroup t'
    SchemeHomOver t f →* SchemeHomOver t' f :=
  letI := G.pointGroup t
  letI := G.pointGroup t'
  MonoidHom.mk' (schemeHomOverComp ψ hψ) (G.mul_natural t t' ψ hψ)

theorem inv_natural (G : RelativeGroupLaw R f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (G.inv t x) = G.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := G.pointGroup t
  letI := G.pointGroup t'
  exact map_inv (compHom G t t' ψ hψ) x

theorem one_val (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (G.one t).1 = t ≫ (G.one (𝟙 _)).1 := by
  rw [← G.one_natural (𝟙 _) t t (Category.comp_id t)]
  rfl

end WeierstrassProjModel.RelativeGroupLaw.RigidUnit

open WeierstrassProjModel.RelativeGroupLaw.RigidUnit in
theorem solution
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]
    (G₀ G₁ : RelativeGroupLaw R (projModelStrCR V))
    (h1 : (G₀.one (𝟙 (Spec (CommRingCat.of R)))).1 = (G₁.one (𝟙 (Spec (CommRingCat.of R)))).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (projModelStrCR V)) :
    G₀.mul t x y = G₁.mul t x y := by

  have hone : ∀ {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R)), G₀.one t' = G₁.one t' := by
    intro T' t'
    apply Subtype.ext
    rw [one_val G₀ t', one_val G₁ t', h1]

  let p := projModelStrCR V
  let e : Spec (CommRingCat.of R) ⟶ projModelCR V := (G₁.one (𝟙 _)).1
  have he : e ≫ p = 𝟙 _ := (G₁.one (𝟙 _)).2
  let t₀ : pullback p p ⟶ Spec (CommRingCat.of R) := pullback.fst p p ≫ p
  let x₀ : SchemeHomOver t₀ p := ⟨pullback.fst p p, rfl⟩
  let y₀ : SchemeHomOver t₀ p := ⟨pullback.snd p p, pullback.condition.symm⟩
  let δ : SchemeHomOver t₀ p := G₁.mul t₀ (G₀.mul t₀ x₀ y₀) (G₁.inv t₀ (G₁.mul t₀ x₀ y₀))

  have pull : ∀ (ψ : projModelCR V ⟶ pullback p p) (hψ : ψ ≫ t₀ = p),
      (schemeHomOverComp ψ hψ x₀ = G₁.one p ∨ schemeHomOverComp ψ hψ y₀ = G₁.one p) →
      ψ ≫ δ.1 = p ≫ e := by
    intro ψ hψ hcase
    have hval : (schemeHomOverComp ψ hψ δ).1 = ψ ≫ δ.1 := rfl
    rw [← hval]
    have : schemeHomOverComp ψ hψ δ = G₁.one p := by
      letI := G₁.pointGroup p
      simp only [δ, G₁.mul_natural, G₀.mul_natural, inv_natural]
      rcases hcase with h | h
      · rw [h, ← hone p, G₀.one_mul, hone p, G₁.one_mul]
        exact mul_inv_cancel (G := SchemeHomOver p p) _
      · rw [h, ← hone p, G₀.mul_one, hone p, G₁.mul_one]
        exact mul_inv_cancel (G := SchemeHomOver p p) _
    rw [this, one_val]

  have hconst : pullback.lift (𝟙 (projModelCR V)) (projModelStrCR V ≫ e)
      (by rw [Category.id_comp, Category.assoc, he, Category.comp_id]) ≫ δ.1 = projModelStrCR V ≫ e := by
    refine pull _ (by rw [← Category.assoc, pullback.lift_fst, Category.id_comp]) (Or.inr (Subtype.ext ?_))
    show pullback.lift (𝟙 (projModelCR V)) (projModelStrCR V ≫ e) _ ≫ pullback.snd p p = (G₁.one p).1
    rw [pullback.lift_snd, one_val]
  have hrig := WeierstrassProjModel.eq_snd_comp_of_comp_eq_const_of_isElliptic V e he δ.1 δ.2 hconst

  have hconst' : pullback.lift (projModelStrCR V ≫ e) (𝟙 (projModelCR V))
      (by rw [Category.assoc, he, Category.comp_id, Category.id_comp]) ≫ δ.1 = projModelStrCR V ≫ e := by
    refine pull _ (by rw [← Category.assoc, pullback.lift_fst, Category.assoc, he, Category.comp_id])
      (Or.inl (Subtype.ext ?_))
    show pullback.lift (projModelStrCR V ≫ e) (𝟙 (projModelCR V)) _ ≫ pullback.fst p p = (G₁.one p).1
    rw [pullback.lift_fst, one_val]
  rw [hconst'] at hrig

  have hδ : δ = G₁.one t₀ := by
    apply Subtype.ext
    rw [hrig, one_val, ← Category.assoc]
    congr 1
    exact pullback.condition.symm
  have huniv : G₀.mul t₀ x₀ y₀ = G₁.mul t₀ x₀ y₀ := by
    letI := G₁.pointGroup t₀
    exact mul_inv_eq_one.mp hδ

  let ψ : T ⟶ pullback p p := pullback.lift x.1 y.1 (x.2.trans y.2.symm)
  have hψ : ψ ≫ t₀ = t := by simp only [ψ, t₀, pullback.lift_fst_assoc]; exact x.2
  have hx : schemeHomOverComp ψ hψ x₀ = x := Subtype.ext (pullback.lift_fst _ _ _)
  have hy : schemeHomOverComp ψ hψ y₀ = y := Subtype.ext (pullback.lift_snd _ _ _)
  calc G₀.mul t x y = G₀.mul t (schemeHomOverComp ψ hψ x₀) (schemeHomOverComp ψ hψ y₀) := by rw [hx, hy]
    _ = schemeHomOverComp ψ hψ (G₀.mul t₀ x₀ y₀) := (G₀.mul_natural t₀ t ψ hψ x₀ y₀).symm
    _ = schemeHomOverComp ψ hψ (G₁.mul t₀ x₀ y₀) := by rw [huniv]
    _ = G₁.mul t (schemeHomOverComp ψ hψ x₀) (schemeHomOverComp ψ hψ y₀) := G₁.mul_natural t₀ t ψ hψ x₀ y₀
    _ = G₁.mul t x y := by rw [hx, hy]

end S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_of_isElliptic
end P2MW
export P2MW.S_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_of_isElliptic (solution)
