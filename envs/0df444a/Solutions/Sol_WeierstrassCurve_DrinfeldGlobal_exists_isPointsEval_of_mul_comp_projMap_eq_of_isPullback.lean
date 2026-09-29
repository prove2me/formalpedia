-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/9d2906ef-f79a-5a28-9142-e3de26e1913b

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback

set_option autoImplicit false

universe u

p2m_open "AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback.WeierstrassCurve.DrinfeldGlobal"

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map_map map toAffine Affine.Point Affine.Point.map Projective baseChange"
namespace DrinfeldGlobal
p2m_export "WeierstrassCurve.DrinfeldGlobal" "base IsCoefficientHom"
p2m_open "WeierstrassCurve.DrinfeldGlobal WeierstrassCurve"

namespace GT3Aux

def castOver {R : Type u} [CommRing R] {X Y : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of R)}
    {t₁ t₂ : Y ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) (x : SchemeHomOver t₁ p) : SchemeHomOver t₂ p :=
  ⟨x.1, x.2.trans h⟩

@[scoped simp] theorem castOver_val {R : Type u} [CommRing R] {X Y : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of R)}
    {t₁ t₂ : Y ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) (x : SchemeHomOver t₁ p) : (castOver h x).1 = x.1 := rfl

theorem mul_castOver {R : Type u} [CommRing R] {X Y : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R p) {t₁ t₂ : Y ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂) (x y : SchemeHomOver t₁ p) :
    G.mul t₂ (castOver h x) (castOver h y) = castOver h (G.mul t₁ x y) := by
  subst h; rfl

def pointCongr {F : Type u} [Field F] {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) :
    W₁.toAffine.Point → W₂.toAffine.Point
  | .zero => .zero
  | .some x y hxy => .some x y (h ▸ hxy)

theorem pointCongr_rfl {F : Type u} [Field F] {W₁ : WeierstrassCurve F} (P : W₁.toAffine.Point) :
    pointCongr rfl P = P := by
  cases P <;> rfl

def pointCongrEquiv {F : Type u} [Field F] {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) :
    W₁.toAffine.Point ≃ W₂.toAffine.Point where
  toFun := pointCongr h
  invFun := pointCongr h.symm
  left_inv P := by subst h; rw [pointCongr_rfl, pointCongr_rfl]
  right_inv P := by subst h; rw [pointCongr_rfl, pointCongr_rfl]

theorem pointCongr_add {F : Type u} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂)
    (P Q : W₁.toAffine.Point) : pointCongr h (P + Q) = pointCongr h P + pointCongr h Q := by
  subst h; simp only [pointCongr_rfl]

section Square

variable {T T' : Type u} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T')
  (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
  (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
    (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
  (hP : IsPullback (Proj.map φ hφ) (projModelStrCR (W.map f)) (projModelStrCR W)
    (Spec.map (CommRingCat.ofHom f)))
  (F : Type u) [Field F] [Algebra T' F] [Algebra T F]
  (halg : (algebraMap T' F).comp f = algebraMap T F)

include halg in
theorem specMap_comp_eq :
    Spec.map (CommRingCat.ofHom (algebraMap T' F)) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom (algebraMap T F)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, halg]

def push (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T' F))) (projModelStrCR (W.map f))) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T F))) (projModelStrCR W) :=
  castOver (specMap_comp_eq f F halg)
    ⟨x.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hP.w, ← Category.assoc, x.2]⟩

@[scoped simp] theorem push_val (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T' F))) (projModelStrCR (W.map f))) :
    (push W f φ hφ hP F halg x).1 = x.1 ≫ Proj.map φ hφ := rfl

def pull (y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T F))) (projModelStrCR W)) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T' F))) (projModelStrCR (W.map f)) :=
  ⟨hP.lift y.1 (Spec.map (CommRingCat.ofHom (algebraMap T' F))) (by rw [y.2, specMap_comp_eq f F halg]),
    hP.lift_snd _ _ _⟩

def pushEquiv : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T' F))) (projModelStrCR (W.map f)) ≃
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T F))) (projModelStrCR W) where
  toFun := push W f φ hφ hP F halg
  invFun := pull W f φ hφ hP F halg
  left_inv x := by
    apply Subtype.ext
    refine hP.hom_ext ?_ ?_
    · simp only [pull, push_val, hP.lift_fst]
    · rw [x.2]; simp only [pull, hP.lift_snd]
  right_inv y := by
    apply Subtype.ext
    simp only [push_val, pull, hP.lift_fst]

@[scoped simp] theorem pushEquiv_apply_val
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T' F))) (projModelStrCR (W.map f))) :
    (pushEquiv W f φ hφ hP F halg x).1 = x.1 ≫ Proj.map φ hφ := rfl

include halg in
theorem baseChange_map_eq : (W.map f).baseChange F = W.baseChange F := by
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_map, halg]

end Square

end GT3Aux
p2m_reactivate "P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback.WeierstrassCurve.DrinfeldGlobal.GT3Aux"

end WeierstrassCurve.DrinfeldGlobal
p2m_reactivate "P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback.WeierstrassCurve.DrinfeldGlobal.GT3Aux P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback.WeierstrassCurve P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback.WeierstrassCurve.DrinfeldGlobal"
p2m_reactivate "P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback.WeierstrassCurve.DrinfeldGlobal.GT3Aux P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback.WeierstrassCurve"

open WeierstrassCurve.DrinfeldGlobal.GT3Aux in
set_option maxHeartbeats 3200000 in
theorem solution
    {T T' : Type u} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W f φ)
    (hP : IsPullback (Proj.map φ hφ) (projModelStrCR (W.map f)) (projModelStrCR W)
      (Spec.map (CommRingCat.ofHom f)))
    (G : RelativeGroupLaw T (projModelStrCR W)) (G' : RelativeGroupLaw T' (projModelStrCR (W.map f)))
    (hmul : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of T')) (x y : SchemeHomOver s (projModelStrCR (W.map f))),
      (G'.mul s x y).1 ≫ Proj.map φ hφ =
        (G.mul (s ≫ Spec.map (CommRingCat.ofHom f))
          ⟨x.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hP.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ Proj.map φ hφ, by rw [Category.assoc, hP.w, ← Category.assoc, y.2]⟩).1)
    (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra T F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T F))) (projModelStrCR W) ≃
        (W.baseChange F).toAffine.Point)
    (hev : IsPointsEval W G ev) :
    ∃ ev' : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra T' F],
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap T' F))) (projModelStrCR (W.map f)) ≃
          ((W.map f).baseChange F).toAffine.Point,
      IsPointsEval (W.map f) G' ev' := by
  classical

  refine ⟨fun F _ _ _ =>
    letI : Algebra T F := ((algebraMap T' F).comp f).toAlgebra
    (pushEquiv W f φ hφ hP F rfl).trans ((ev F).trans (pointCongrEquiv (baseChange_map_eq W f F rfl)).symm),
    ?_, ?_⟩
  ·
    intro F _ _ _ P Q
    letI : Algebra T F := ((algebraMap T' F).comp f).toAlgebra
    have hWF : W.baseChange F = (W.map f).baseChange F := (baseChange_map_eq W f F rfl).symm
    show pointCongr hWF (ev F (pushEquiv W f φ hφ hP F rfl (G'.mul _ P Q))) =
      pointCongr hWF (ev F (pushEquiv W f φ hφ hP F rfl P)) + pointCongr hWF (ev F (pushEquiv W f φ hφ hP F rfl Q))
    rw [← pointCongr_add, ← hev.1]
    congr 2

    apply Subtype.ext
    have h := hmul (Spec.map (CommRingCat.ofHom (algebraMap T' F))) P Q
    rw [pushEquiv_apply_val, h]
    show _ = (G.mul _ (castOver (specMap_comp_eq f F rfl) _) (castOver (specMap_comp_eq f F rfl) _)).1
    rw [mul_castOver, castOver_val]
  ·
    intro F _ _ _ σ P
    letI : Algebra T F := ((algebraMap T' F).comp f).toAlgebra

    let σT : F ≃ₐ[T] F := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun r => σ.commutes (f r))
    have hσ : (σT : F →+* F) = (σ : F →+* F) := RingHom.ext fun _ => rfl
    have hWF : W.baseChange F = (W.map f).baseChange F := (baseChange_map_eq W f F rfl).symm
    show pointCongr hWF (ev F (pushEquiv W f φ hφ hP F rfl (galTwist σ P))) =
      WeierstrassCurve.Affine.Point.map (σ : F →ₐ[T'] F) (pointCongr hWF (ev F (pushEquiv W f φ hφ hP F rfl P)))
    have htw : pushEquiv W f φ hφ hP F rfl (galTwist σ P) = galTwist σT (pushEquiv W f φ hφ hP F rfl P) := by
      apply Subtype.ext
      simp only [pushEquiv_apply_val, galTwist, schemeHomOverComp, hσ, Category.assoc]
    rw [htw, hev.2]

    generalize ev F (pushEquiv W f φ hφ hP F rfl P) = R₀
    rcases R₀ with _ | ⟨x, y, hxy⟩
    · rfl
    · rfl

end
p2m_reactivate "P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback.WeierstrassCurve.DrinfeldGlobal.GT3Aux P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback.WeierstrassCurve P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback.WeierstrassCurve.DrinfeldGlobal"

end S_WeierstrassCurve_DrinfeldGlobal_exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isPointsEval_of_mul_comp_projMap_eq_of_isPullback (solution)
