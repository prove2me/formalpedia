-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TG.toW_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:37.488353+00:00
-- url     : https://prove2.me/submissions/aede7b99-51a0-45b8-8b48-85fd0085858d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenFlat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_appLE_of_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_app_fst_jF_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
noncomputable section
variable {R : Type} [CommRing R] [IsDomain R]
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
theorem _root_.solution {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] (V : X.Opens)
    {r : R} (hr : r ≠ 0) {y : Γ(X, V)} (h : toW p V r * y = 0) : y = 0 := by
  set π := pullback.fst p (jF R)
  have hu : IsUnit ((π.app V).hom (toW p V r)) := by
    have e1 : (π.app V).hom (toW p V r) =
        ((pullback.snd p (jF R) ≫ jF R).appLE ⊤ (π ⁻¹ᵁ V) le_top).hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
      rw [toW, RingHom.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE]
      erw [Scheme.Hom.appLE_comp_appLE]
      rw [appLE_of_eq pullback.condition]
    have e2 : (pullback.snd p (jF R) ≫ jF R).appLE ⊤ (π ⁻¹ᵁ V) le_top =
        (jF R).appLE ⊤ (jF R ⁻¹ᵁ ⊤) le_rfl ≫ (pullback.snd p (jF R)).appLE (jF R ⁻¹ᵁ ⊤) (π ⁻¹ᵁ V) le_top := by
      erw [Scheme.Hom.appLE_comp_appLE]
    have e3 : (jF R).appLE ⊤ (jF R ⁻¹ᵁ ⊤) le_rfl =
        (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫
          (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv := by
      rw [Scheme.Hom.appLE_eq_app, ← Scheme.Hom.appTop,
        (Iso.eq_comp_inv _).2 (Scheme.ΓSpecIso_naturality _), Category.assoc]
    have eR : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = r := by
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl
    have hK : IsUnit (algebraMap R (FractionRing R) r) :=
      isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
    have e4 : ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫
          (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
        (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) r) := by
      rw [CommRingCat.comp_apply, CommRingCat.comp_apply, eR]; rfl
    rw [e1, e2, CommRingCat.comp_apply, e3]
    erw [e4]
    exact (hK.map _).map _
  have hinj := app_fst_jF_injective p V
  apply hinj
  have := congrArg (π.app V).hom h
  rw [map_mul, map_zero] at this
  rw [map_zero]
  exact (IsUnit.mul_right_eq_zero hu).1 this
end ReciprocityTheory.ChartRestriction.G.DVR.TG
