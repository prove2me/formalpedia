-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.unit_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:22:24.489946+00:00
-- url     : https://prove2.me/submissions/3132a3ba-1415-43b5-a840-c34d007cb931

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
theorem _root_.solution {V : X.Opens} {a b : Γ(X, V)ˣ} (h : ∀ x ∈ V, gm (𝟙 X) x V a = gm (𝟙 X) x V b) : a = b := by
  apply Units.ext
  apply TopCat.Presheaf.section_ext X.sheaf V
  intro x hx
  have e := congrArg Units.val (h x hx)
  rw [gm_val _ _ _ hx, gm_val _ _ _ hx] at e
  exact e
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
