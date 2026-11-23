-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TG.app_toW_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:29.948157+00:00
-- url     : https://prove2.me/submissions/11a7448c-d7c7-4ecf-ae90-1eb9cdf059df

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenFlat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenThick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_appLE_of_eq


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
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
theorem _root_.solution {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (J : Ideal R) (W : X.Opens)
    {r : R} (hr : r ∈ J) : (pullback.fst p (tq J)).app W (toW p W r) = 0 := by
  have e1 : (pullback.fst p (tq J)).app W (toW p W r) =
      ((pullback.snd p (tq J) ≫ tq J).appLE ⊤ (pullback.fst p (tq J) ⁻¹ᵁ W) le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    rw [toW, RingHom.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE]
    erw [Scheme.Hom.appLE_comp_appLE]
    rw [appLE_of_eq pullback.condition]
  have e2 : (pullback.snd p (tq J) ≫ tq J).appLE ⊤ (pullback.fst p (tq J) ⁻¹ᵁ W) le_top =
      (tq J).appLE ⊤ (tq J ⁻¹ᵁ ⊤) le_rfl ≫
        (pullback.snd p (tq J)).appLE (tq J ⁻¹ᵁ ⊤) (pullback.fst p (tq J) ⁻¹ᵁ W) le_top := by
    erw [Scheme.Hom.appLE_comp_appLE]
  have e3 : (tq J).appLE ⊤ (tq J ⁻¹ᵁ ⊤) le_rfl =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv := by
    rw [Scheme.Hom.appLE_eq_app, ← Scheme.Hom.appTop,
      (Iso.eq_comp_inv _).2 (Scheme.ΓSpecIso_naturality _), Category.assoc]
  have eR : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = r := by
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl
  have e4 : ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = 0 := by
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, eR]
    erw [Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
  rw [e1, e2, CommRingCat.comp_apply, e3]
  erw [e4, map_zero]
end ReciprocityTheory.ChartRestriction.G.DVR.TG
