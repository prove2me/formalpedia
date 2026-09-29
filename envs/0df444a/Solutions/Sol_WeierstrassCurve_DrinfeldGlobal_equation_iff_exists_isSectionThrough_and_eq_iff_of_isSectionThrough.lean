-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/ced02825-289b-542c-bbf6-42e56087078e

import Mathlib
import Definitions.Def_WeierstrassCurve_PointChart
import Theorems.Thm_WeierstrassProjModel_exists_zChartAway_equiv_coordinateRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel MvPolynomial HomogeneousLocalization
open HomogeneousIdealQuotientGrading WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

namespace SectionThroughBody

variable {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T)

abbrev CR : Type u := Polynomial (Polynomial T) ⧸ Ideal.span {W.toAffine.polynomial}

noncomputable abbrev mkCR : Polynomial (Polynomial T) →+* CR W :=
  Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial})

noncomputable abbrev toChart : T →+* ZChartRing W :=
  (fromZeroRingHom (projModelGradingCR W) (Submonoid.powers (coord W 2))).comp
    (algebraMap T (projModelGradingCR W 0))

theorem exists_equiv :
    ∃ f : ZChartRing W →+* CR W, Function.Bijective f ∧
      (∀ t : T, f (toChart W t) = mkCR W (Polynomial.C (Polynomial.C t))) ∧
      f (xOverZ W) = mkCR W (Polynomial.C Polynomial.X) ∧
      f (yOverZ W) = mkCR W Polynomial.X := by
  obtain ⟨f, hbij, hcomp, hmk⟩ := WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing W
  refine ⟨f, hbij, ?_, ?_, ?_⟩
  · intro t

    exact RingHom.congr_fun hcomp t
  · have hb : (X 0 : MvPolynomial (Fin 3) T) ∈ MvPolynomial.homogeneousSubmodule (Fin 3) T (1 • 1) := by
      simpa using (MvPolynomial.isHomogeneous_X T (0 : Fin 3))
    have := hmk 1 (X 0) hb
    simp [xOverZ] at this
    exact this
  · have hb : (X 1 : MvPolynomial (Fin 3) T) ∈ MvPolynomial.homogeneousSubmodule (Fin 3) T (1 • 1) := by
      simpa using (MvPolynomial.isHomogeneous_X T (1 : Fin 3))
    have := hmk 1 (X 1) hb
    simp [yOverZ] at this
    exact this

theorem specMap_comp_zChartι_comp_str (χ : ZChartRing W →+* T) :
    (Spec.map (CommRingCat.ofHom χ) ≫ zChartι W) ≫ projModelStrCR W =
      Spec.map (CommRingCat.ofHom (χ.comp (toChart W))) := by
  rw [projModelStrCR, Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem over_iff (χ : ZChartRing W →+* T) :
    (Spec.map (CommRingCat.ofHom χ) ≫ zChartι W) ≫ projModelStrCR W = 𝟙 _ ↔ χ.comp (toChart W) = RingHom.id T := by
  rw [specMap_comp_zChartι_comp_str]
  constructor
  · intro h
    have h' : Spec.map (CommRingCat.ofHom (χ.comp (toChart W))) = Spec.map (𝟙 _) := by rw [h, Spec.map_id]
    have h'' := Spec.map_injective h'
    exact congrArg CommRingCat.Hom.hom h''
  · intro h
    rw [h]
    exact Spec.map_id _

theorem retraction_of_isZChartSection {S : Section W} {χ : ZChartRing W →+* T} (h : IsZChartSection S χ) :
    ∀ t : T, χ (toChart W t) = t := by
  have := S.2
  rw [h] at this
  have h2 := (over_iff W χ).1 this
  intro t
  have := congrArg (fun φ : T →+* T => φ t) h2
  simpa only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply] using this

theorem ringHom_CR_ext {g g' : CR W →+* T}
    (hC : ∀ t : T, g (mkCR W (Polynomial.C (Polynomial.C t))) = g' (mkCR W (Polynomial.C (Polynomial.C t))))
    (hx : g (mkCR W (Polynomial.C Polynomial.X)) = g' (mkCR W (Polynomial.C Polynomial.X)))
    (hy : g (mkCR W Polynomial.X) = g' (mkCR W Polynomial.X)) : g = g' := by
  apply Ideal.Quotient.ringHom_ext
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · exact RingHom.ext fun t => hC t
    · exact hx
  · exact hy

noncomputable def ev {x y : T} (hxy : W.toAffine.Equation x y) : CR W →+* T :=
  Ideal.Quotient.lift _ (Polynomial.evalEvalRingHom x y) (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul]
    change Polynomial.evalEval x y W.toAffine.polynomial * _ = 0
    rw [WeierstrassCurve.Affine.Equation] at hxy
    rw [hxy, zero_mul])

theorem ev_mk {x y : T} (hxy : W.toAffine.Equation x y) (p : Polynomial (Polynomial T)) :
    ev W hxy (mkCR W p) = Polynomial.evalEval x y p := by
  rw [ev, Ideal.Quotient.lift_mk]
  rfl

theorem ev_CC {x y : T} (hxy : W.toAffine.Equation x y) (t : T) :
    ev W hxy (mkCR W (Polynomial.C (Polynomial.C t))) = t := by
  rw [ev_mk, Polynomial.evalEval_C, Polynomial.eval_C]

theorem ev_x {x y : T} (hxy : W.toAffine.Equation x y) :
    ev W hxy (mkCR W (Polynomial.C Polynomial.X)) = x := by
  rw [ev_mk, Polynomial.evalEval_C, Polynomial.eval_X]

theorem ev_y {x y : T} (hxy : W.toAffine.Equation x y) :
    ev W hxy (mkCR W Polynomial.X) = y := by
  rw [ev_mk, Polynomial.evalEval_X]

theorem exists_section_of_equation {x y : T} (hxy : W.toAffine.Equation x y) :
    ∃ S : Section W, IsSectionThrough S x y := by
  obtain ⟨f, hbij, hcomp, hfx, hfy⟩ := exists_equiv W
  let χ : ZChartRing W →+* T := (ev W hxy).comp f
  have hχ : χ.comp (toChart W) = RingHom.id T := by
    ext t
    change ev W hxy (f (toChart W t)) = t
    rw [hcomp]
    exact ev_CC W hxy t
  refine ⟨⟨Spec.map (CommRingCat.ofHom χ) ≫ zChartι W, (over_iff W χ).2 hχ⟩, χ, rfl, ?_, ?_⟩
  · change ev W hxy (f (xOverZ W)) = x
    rw [hfx]
    exact ev_x W hxy
  · change ev W hxy (f (yOverZ W)) = y
    rw [hfy]
    exact ev_y W hxy

theorem comp_symm_mk_eq {S : Section W} {χ : ZChartRing W →+* T} (hS : IsZChartSection S χ)
    (f : ZChartRing W →+* CR W) (hbij : Function.Bijective f)
    (hcomp : ∀ t : T, f (toChart W t) = mkCR W (Polynomial.C (Polynomial.C t)))
    (hfx : f (xOverZ W) = mkCR W (Polynomial.C Polynomial.X)) (hfy : f (yOverZ W) = mkCR W Polynomial.X) :
    (χ.comp (RingEquiv.ofBijective f hbij).symm.toRingHom).comp (mkCR W) =
      Polynomial.evalEvalRingHom (χ (xOverZ W)) (χ (yOverZ W)) := by
  set e : ZChartRing W ≃+* CR W := RingEquiv.ofBijective f hbij with he_def
  have he : ∀ a, e a = f a := fun _ => rfl
  have hret := retraction_of_isZChartSection W hS
  have s1 : ∀ t : T, e.symm (mkCR W (Polynomial.C (Polynomial.C t))) = toChart W t := by
    intro t
    apply e.injective
    rw [RingEquiv.apply_symm_apply, he, hcomp]
  have s2 : e.symm (mkCR W (Polynomial.C Polynomial.X)) = xOverZ W := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply, he, hfx]
  have s3 : e.symm (mkCR W Polynomial.X) = yOverZ W := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply, he, hfy]
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext'
    · refine RingHom.ext fun t => ?_
      change χ (e.symm (mkCR W (Polynomial.C (Polynomial.C t)))) =
        Polynomial.evalEval (χ (xOverZ W)) (χ (yOverZ W)) (Polynomial.C (Polynomial.C t))
      rw [s1, hret, Polynomial.evalEval_C, Polynomial.eval_C]
    · change χ (e.symm (mkCR W (Polynomial.C Polynomial.X))) =
        Polynomial.evalEval (χ (xOverZ W)) (χ (yOverZ W)) (Polynomial.C Polynomial.X)
      rw [s2, Polynomial.evalEval_C, Polynomial.eval_X]
  · change χ (e.symm (mkCR W Polynomial.X)) = Polynomial.evalEval (χ (xOverZ W)) (χ (yOverZ W)) Polynomial.X
    rw [s3, Polynomial.evalEval_X]

theorem equation_of_isSectionThrough {S : Section W} {x y : T} (h : IsSectionThrough S x y) :
    W.toAffine.Equation x y := by
  obtain ⟨χ, hS, hx, hy⟩ := h
  obtain ⟨f, hbij, hcomp, hfx, hfy⟩ := exists_equiv W
  have hg := comp_symm_mk_eq W hS f hbij hcomp hfx hfy
  rw [affX] at hx
  rw [affY] at hy
  rw [hx, hy] at hg
  have h0 : (χ.comp (RingEquiv.ofBijective f hbij).symm.toRingHom) (mkCR W W.toAffine.polynomial) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), map_zero]
  have := congrArg (fun φ : Polynomial (Polynomial T) →+* T => φ W.toAffine.polynomial) hg
  change (χ.comp (RingEquiv.ofBijective f hbij).symm.toRingHom) (mkCR W W.toAffine.polynomial) =
    Polynomial.evalEval x y W.toAffine.polynomial at this
  rw [WeierstrassCurve.Affine.Equation, ← this]
  exact h0

theorem coords_eq_of_eq {S : Section W} {x y x' y' : T} (h : IsSectionThrough S x y) (h' : IsSectionThrough S x' y') :
    x = x' ∧ y = y' := by
  obtain ⟨χ, hS, hx, hy⟩ := h
  obtain ⟨χ', hS', hx', hy'⟩ := h'
  have hmono : Spec.map (CommRingCat.ofHom χ) = Spec.map (CommRingCat.ofHom χ') := by
    rw [← cancel_mono (zChartι W)]
    rw [IsZChartSection] at hS hS'
    rw [← hS, ← hS']
  have hχ : χ = χ' := by
    have := Spec.map_injective hmono
    exact congrArg CommRingCat.Hom.hom this
  subst hχ
  exact ⟨hx.symm.trans hx', hy.symm.trans hy'⟩

theorem eq_of_coords_eq {S S' : Section W} {x y : T} (h : IsSectionThrough S x y) (h' : IsSectionThrough S' x y) :
    S = S' := by
  obtain ⟨χ, hS, hx, hy⟩ := h
  obtain ⟨χ', hS', hx', hy'⟩ := h'
  obtain ⟨f, hbij, hcomp, hfx, hfy⟩ := exists_equiv W
  have hg := comp_symm_mk_eq W hS f hbij hcomp hfx hfy
  have hg' := comp_symm_mk_eq W hS' f hbij hcomp hfx hfy
  rw [affX] at hx hx'
  rw [affY] at hy hy'
  rw [hx, hy] at hg
  rw [hx', hy', ← hg] at hg'

  have h1 : χ'.comp (RingEquiv.ofBijective f hbij).symm.toRingHom =
      χ.comp (RingEquiv.ofBijective f hbij).symm.toRingHom :=
    Ideal.Quotient.ringHom_ext hg'
  have hχ : χ = χ' := by
    ext a
    have := congrArg (fun φ : CR W →+* T => φ (RingEquiv.ofBijective f hbij a)) h1
    have key : (RingEquiv.ofBijective f hbij).symm (RingEquiv.ofBijective f hbij a) = a :=
      (RingEquiv.ofBijective f hbij).symm_apply_apply a
    simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, Function.comp_apply, key] at this
    exact this.symm
  subst hχ
  apply Subtype.ext
  rw [IsZChartSection] at hS hS'
  rw [hS, hS']

end SectionThroughBody

open SectionThroughBody in
theorem solution
    {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T) :
    (∀ x y : T, W.toAffine.Equation x y ↔ ∃ S : Section W, IsSectionThrough S x y) ∧
    (∀ (S S' : Section W) (x y x' y' : T), IsSectionThrough S x y → IsSectionThrough S' x' y' →
      (S = S' ↔ (x = x' ∧ y = y'))) := by
  refine ⟨fun x y => ⟨fun h => exists_section_of_equation W h, ?_⟩, ?_⟩
  · rintro ⟨S, hS⟩
    exact equation_of_isSectionThrough W hS
  · intro S S' x y x' y' hS hS'
    constructor
    · rintro rfl
      exact coords_eq_of_eq W hS hS'
    · rintro ⟨rfl, rfl⟩
      exact eq_of_coords_eq W hS hS'

end S_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough (solution)
