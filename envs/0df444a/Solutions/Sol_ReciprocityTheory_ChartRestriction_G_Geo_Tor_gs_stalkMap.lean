-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_stalkMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:34.65905+00:00
-- url     : https://prove2.me/submissions/338818ea-a206-4f27-86f4-547e8b131d77

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
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi
variable {V : Type} [CommRing V] {X Z : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (f : Γ(X, U)) :
    gs r z U f = (r.stalkMap z).hom (gs (𝟙 X) (r z) U f) := by
  unfold gs
  rw [dif_pos h, dif_pos (show (𝟙 X : X ⟶ X) (r z) ∈ U from h)]
  rw [← Scheme.Hom.germ_stalkMap_apply]
  first
  | rfl
  | (congr 1; simp)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
