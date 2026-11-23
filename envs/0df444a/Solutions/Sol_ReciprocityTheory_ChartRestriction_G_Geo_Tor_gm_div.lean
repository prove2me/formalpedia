-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:57.091798+00:00
-- url     : https://prove2.me/submissions/8afb34b9-a6f2-4c96-8727-5f8540f4f96d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {X X' Y Y' : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {Z : Scheme.{0}} (A B : LB Y) (r : Z ⟶ Y) (z : Z) (p q : B.ι × A.ι)
    (hm : r z ∈ B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2)) :
    gm r z (B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2)) ((LB.div B A).g p q) =
      gm r z _ (B.g p.1 q.1) * (gm r z _ (A.g p.2 q.2))⁻¹ :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hm _)
    ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z _ hm _))))
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
