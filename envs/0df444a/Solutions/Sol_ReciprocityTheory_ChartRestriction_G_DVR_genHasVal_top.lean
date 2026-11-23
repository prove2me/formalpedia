-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.genHasVal_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:51.431038+00:00
-- url     : https://prove2.me/submissions/7432f81b-24fe-44a9-b738-107de77fa042

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
set_option maxHeartbeats 1000000
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {X : Scheme.{0}} (L : LB X) {Ix : Type} [Fintype Ix]
    (φ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb L (fun k => jK V ≫ φ k) ε)) {n : ℤ}
    (hn : GenHasVal ϖ L φ (fun k => jK V ≫ φ k) (fun _ => rfl) ε t n) (j₀ : Ix → L.ι)
    (htop : LB.wchart L φ j₀ = ⊤) (hK : (⊤ : (Spec (CommRingCat.of (FractionRing V))).Opens) ≤
      LB.wchart L (fun k => jK V ≫ φ k) j₀) :
    ∃ c : FractionRing V, HasVal ϖ c n ∧ ∃ eV : Vˣ,
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).hom.hom (res hK (t.s j₀)).val =
        c * algebraMap V (FractionRing V) (eV : V) := by
  obtain ⟨e, he, c, hc, hte⟩ := hn
  have hV : (⊤ : (Spec (CommRingCat.of V)).Opens) ≤ LB.wchart L φ j₀ := htop ▸ le_rfl
  set E : Γ(Spec (CommRingCat.of V), ⊤)ˣ := res hV (e.s j₀) with hE
  set eV : Vˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom E with heV
  refine ⟨c, hc, eV, ?_⟩
  have h1 := congrArg ((Spec (CommRingCat.of (FractionRing V))).presheaf.map (homOfLE hK).op).hom (hte j₀)
  erw [map_mul] at h1
  have hA : ((Spec (CommRingCat.of (FractionRing V))).presheaf.map (homOfLE hK).op).hom (t.s j₀).val =
      (res hK (t.s j₀)).val := rfl
  rw [hA] at h1
  rw [h1]
  erw [map_mul]
  congr 1
  · simp only [resTop, scal, Scheme.Hom.id_appTop, ← CommRingCat.comp_apply, ← Functor.map_comp]
    have : (homOfLE (le_top : LB.wchart L (fun k => jK V ≫ φ k) j₀ ≤ ⊤)).op ≫ (homOfLE hK).op =
        𝟙 (Opposite.op (⊤ : (Spec (CommRingCat.of (FractionRing V))).Opens)) := Subsingleton.elim _ _
    rw [Category.id_comp, ← Functor.map_comp]
    erw [this, CategoryTheory.Functor.map_id]
    simp
  · simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe, heV, hE, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe]
    have hnat := congrArg (fun f => (CommRingCat.Hom.hom f)
        (((Spec (CommRingCat.of V)).presheaf.map (homOfLE hV).op).hom (e.s j₀).val))
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))
    simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at hnat
    erw [← hnat]
    rw [CommRingCat.comp_apply]
    congr 1
end ReciprocityTheory.ChartRestriction.G.DVR
