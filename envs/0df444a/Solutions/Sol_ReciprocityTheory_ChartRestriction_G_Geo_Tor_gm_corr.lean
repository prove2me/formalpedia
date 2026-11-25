-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_corr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:55:17.391124+00:00
-- url     : https://prove2.me/submissions/e666672f-82d9-4c3b-aeb1-bb9ef5bcfbb1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_OLinBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
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
private lemma gm_res_toroidal_compactification {A B : Scheme.{0}} (f : A ⟶ B) (y : A) {U V : B.Opens} (hVU : V ≤ U)
    (hy : f y ∈ V) (u : Γ(B, U)ˣ) : gm f y V (res hVU u) = gm f y U u := by
  ext1
  rw [gm, gm, dif_pos hy, dif_pos (hVU hy)]
  simp only [MonoidHom.comp_apply, Units.coe_map, res, pullU, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact germ_app_presheaf_map_eq_germ_app f y hVU hy _
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
theorem _root_.solution {Z : Scheme.{0}} (L : LB X) {φ φ' : PUnit → (Y ⟶ X)} {ε ε' : PUnit → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε')} (h : LB.Gen.Corr L φ ε φ' ε' t t') (r : Z ⟶ Y) (z : Z) (j : L.ι)
    (h₁ : r z ∈ LB.wchart L φ (fun _ => j)) (h₂ : r z ∈ LB.wchart L φ' (fun _ => j)) :
    gm r z (LB.wchart L φ (fun _ => j)) (t.s (fun _ => j)) = gm r z (LB.wchart L φ' (fun _ => j)) (t'.s (fun _ => j)) := by
  have hC : ∀ (ψ : PUnit → (Y ⟶ X)) (j' : PUnit → L.ι), LB.Coh L ψ j' := fun _ j' k₁ k₂ _ => by
    cases k₁; cases k₂; rfl
  have hc := h (fun _ => j) (fun _ => j) (hC _ _) (hC _ _) (fun _ _ _ => rfl)
  have hW : r z ∈ LB.wchart L φ (fun _ => j) ⊓ LB.wchart L φ' (fun _ => j) :=
    TopologicalSpace.Opens.mem_inf.2 ⟨h₁, h₂⟩
  exact ((gm_res_toroidal_compactification r z inf_le_left hW _).symm.trans (congrArg (gm r z _) hc)).trans
    (gm_res_toroidal_compactification r z inf_le_right hW _)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
