-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:22:21.861861+00:00
-- url     : https://prove2.me/submissions/294e467b-4c53-4f76-945a-6aef2fa9291f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_val

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
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (f : Y ⟶ X) (y : Y) {U V : X.Opens} (hle : V ≤ U) (h : f y ∈ V) (a : Γ(X, U)ˣ) :
    gm f y V (res hle a) = gm f y U a := by
  apply Units.ext
  rw [gm_val f y V h, gm_val f y U (hle h)]
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  have e1 := Scheme.Hom.naturality f (homOfLE hle).op
  rw [← Y.presheaf.germ_res (homOfLE (Scheme.Hom.preimage_mono f hle)) y h]
  rw [CommRingCat.comp_apply]
  congr 1
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, e1]
  rfl
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
