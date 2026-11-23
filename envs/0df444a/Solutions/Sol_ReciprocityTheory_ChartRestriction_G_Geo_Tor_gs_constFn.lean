-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_constFn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:57.236343+00:00
-- url     : https://prove2.me/submissions/07ed8743-19e6-45df-8c62-c839f45a0c3e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_appLE

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
theorem _root_.solution (p : X ⟶ Sp V) (W : X.Opens) (r : Z ⟶ X) (z : Z) (hz : r z ∈ W) (a : V) :
    gs r z W (constFn p W a) = cst (r ≫ p) z a := by
  first
    | (unfold constFn cst; exact gs_appLE p ⊤ W le_top r z hz _)
    | (unfold constFn cst; rw [← gs_appLE p ⊤ W le_top r z hz]; rfl)
    | (simp only [constFn, cst]; exact gs_appLE p ⊤ W le_top r z hz _)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
