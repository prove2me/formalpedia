-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_ext_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:21.186404+00:00
-- url     : https://prove2.me/submissions/d2cdce35-8563-4023-8f08-30187768b9f2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
theorem _root_.solution {X Y : Scheme.{0}} (κ : Y ⟶ X) [IsOpenImmersion κ] (V : Y.Opens) (a : Γ(Y, V)ˣ) :
    ∃ b : Γ(X, κ ''ᵁ V)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ V → gm (r ≫ κ) z (κ ''ᵁ V) b = gm r z V a := by
  refine ⟨Units.map (κ.appIso V).inv.hom.toMonoidHom a, fun Z r z hz => ?_⟩
  have hm : r z ∈ κ ⁻¹ᵁ (κ ''ᵁ V) := ⟨r z, hz, rfl⟩
  have e : pullU κ (κ ''ᵁ V) (Units.map (κ.appIso V).inv.hom.toMonoidHom a) = res (κ.preimage_image_eq V).le a :=
    Units.ext (congrArg (fun q => q.hom a.val) (κ.appIso_inv_app V))
  rw [← gm_pull r κ z _ hm, e, gm_res r z _ hm]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
