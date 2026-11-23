-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_appLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:44.538247+00:00
-- url     : https://prove2.me/submissions/8aa9ff07-7a01-4870-815d-0e52d861b04d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi
variable {V : Type} [CommRing V] {X Z : Scheme.{0}}
private lemma germ_app_presheaf_map_eq_germ_app {A B : Scheme.{0}} (f : A ⟶ B) (y : A) {U V : B.Opens} (hVU : V ≤ U)
    (hy : f y ∈ V) (a : Γ(B, U)) :
    (A.presheaf.germ (f ⁻¹ᵁ V) y hy).hom ((f.app V).hom ((B.presheaf.map (homOfLE hVU).op).hom a)) =
      (A.presheaf.germ (f ⁻¹ᵁ U) y (hVU hy)).hom ((f.app U).hom a) := by
  have nat := congrArg (fun g => g.hom a) (Scheme.Hom.naturality f (homOfLE hVU).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at nat
  rw [nat]
  first
    | exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
    | exact TopCat.Presheaf.germ_res_apply _ _ _ _ _ _
    | (erw [TopCat.Presheaf.germ_res_apply])
    | (simp; done)
private lemma germ_app_app_eq_germ_app_comp {A B C : Scheme.{0}} (r : A ⟶ B) (h : B ⟶ C) (y : A) (W : C.Opens)
    (hy : h (r y) ∈ W) (a : Γ(C, W)) :
    (A.presheaf.germ (r ⁻¹ᵁ h ⁻¹ᵁ W) y hy).hom ((r.app (h ⁻¹ᵁ W)).hom ((h.app W).hom a)) =
      (A.presheaf.germ ((r ≫ h) ⁻¹ᵁ W) y hy).hom (((r ≫ h).app W).hom a) := by
  first
    | rfl
    | (simp only [Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply]; rfl)
    | (simp [Scheme.Hom.comp_app]; done)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi
variable {V : Type} [CommRing V] {X Z : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {Y : Scheme.{0}} (q : Y ⟶ X) (U : X.Opens) (W : Y.Opens) (e : W ≤ q ⁻¹ᵁ U) (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ W) (f : Γ(X, U)) : gs r z W ((q.appLE U W e).hom f) = gs (r ≫ q) z U f := by
  unfold gs
  rw [dif_pos hz, dif_pos (show (r ≫ q) z ∈ U from e hz)]
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
  exact (germ_app_presheaf_map_eq_germ_app r z e hz _).trans (germ_app_app_eq_germ_app_comp r q z U (e hz) f)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
