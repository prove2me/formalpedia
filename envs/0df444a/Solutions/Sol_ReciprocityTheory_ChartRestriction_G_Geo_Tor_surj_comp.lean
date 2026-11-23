-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.surj_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:17.515834+00:00
-- url     : https://prove2.me/submissions/ae779d79-03f6-4e02-9770-c2257fedd9ca

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {X Y Z : Scheme.{0}} {p : X ⟶ Y} {q : Y ⟶ Z} (hp : Function.Surjective p.appTop.hom)
    (hq : Function.Surjective q.appTop.hom) : Function.Surjective (p ≫ q).appTop.hom := by
  first
    | (rw [Scheme.Hom.comp_appTop]; exact hp.comp hq)
    | (rw [Scheme.comp_appTop]; exact hp.comp hq)
    | (simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]; exact hp.comp hq)
    | simpa using hp.comp hq
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
