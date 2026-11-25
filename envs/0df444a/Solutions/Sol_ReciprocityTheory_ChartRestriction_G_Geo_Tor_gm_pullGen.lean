-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_pullGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:49:48.2629+00:00
-- url     : https://prove2.me/submissions/d38bc37f-3702-4355-bfde-5a81c6a57dd2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_OLinBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
section Grp
variable {S S' : Scheme.{0}}
end Grp
section Iso
variable {X Y Y' : Scheme.{0}}
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
end Iso
section Field
variable {F : Type} [Field F] {X : Scheme.{0}}
variable {B B' B₀ : Scheme.{0}} {M : LB B} {M' : LB B'} {M₀ : LB B₀} {K : Type} [Fintype K] {ε : K → ℤ}
end Field
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {X Y Y' : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {Z Z' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y) (r : Z' ⟶ Z) (z : Z') (j : K → L.ι)
    (hz : r z ∈ LB.wchart L (fun k => h ≫ φ k) j) :
    gm r z (LB.wchart L (fun k => h ≫ φ k) j) ((LB.pullGen L φ ε t h).s j) = gm (r ≫ h) z (LB.wchart L φ j) (t.s j) := by
  have hz' : h (r z) ∈ LB.wchart L φ j := Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz k
  have hle : LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  ext1
  rw [gm, gm, dif_pos hz, dif_pos (show (r ≫ h) z ∈ LB.wchart L φ j from hz')]
  simp only [LB.pullGen, MonoidHom.comp_apply, Units.coe_map, res, pullU, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe]
  exact (germ_app_presheaf_map_eq_germ_app r z hle hz _).trans (germ_app_app_eq_germ_app_comp r h z _ hz' _)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
