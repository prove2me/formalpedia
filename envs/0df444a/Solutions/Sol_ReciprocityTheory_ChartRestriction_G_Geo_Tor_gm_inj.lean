-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:19.206257+00:00
-- url     : https://prove2.me/submissions/e546c724-b8da-4f28-9ac1-7181713252d4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {X Z : Scheme.{0}} (κ : Z ⟶ X) [IsOpenImmersion κ] (z : Z) {U U' : X.Opens} (h : κ z ∈ U) (h' : κ z ∈ U')
    {a : Γ(X, U)ˣ} {b : Γ(X, U')ˣ} (e : gm κ z U a = gm κ z U' b) :
    gm (𝟙 X) (κ z) U a = gm (𝟙 X) (κ z) U' b := by
  have key : ∀ (V : X.Opens) (hV : κ z ∈ V) (c : Γ(X, V)ˣ),
      (κ.stalkMap z).hom ((gm (𝟙 X) (κ z) V c : (X.presheaf.stalk (κ z))ˣ) : X.presheaf.stalk (κ z)) =
        ((gm κ z V c : (Z.presheaf.stalk z)ˣ) : Z.presheaf.stalk z) := by
    intro V hV c
    have h1 : (𝟙 X : X ⟶ X) (κ z) ∈ V := hV
    simp only [gm, dif_pos hV, dif_pos h1, MonoidHom.comp_apply, Units.coe_map, pullU, MonoidHom.coe_coe]
    clear e h h' a b U U'
    first
      | (show (κ.stalkMap z).hom (X.presheaf.germ V (κ z) hV (c : Γ(X, V))) = _
         rw [Scheme.Hom.germ_stalkMap_apply]; rfl)
      | (show (κ.stalkMap z).hom (X.presheaf.germ V (κ z) hV (c : Γ(X, V))) = _
         simp [Scheme.Hom.germ_stalkMap_apply]; done)
      | (show (κ.stalkMap z).hom (X.presheaf.germ V (κ z) hV (c : Γ(X, V))) = _
         clear * -; done)
  have hinj : Function.Injective (κ.stalkMap z).hom := by
    first
      | exact (ConcreteCategory.bijective_of_isIso (κ.stalkMap z)).1
      | exact (asIso (κ.stalkMap z)).commRingCatIsoToRingEquiv.injective
  apply Units.ext
  apply hinj
  rw [key U h a, key U' h' b]
  exact congrArg Units.val e
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
