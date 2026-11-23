-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.unitOn_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:51.483261+00:00
-- url     : https://prove2.me/submissions/238425dc-18f8-49ed-af5e-9dab04dffbaf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_AlphaPair

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution {K : Type} [CommRing K] : Function.Injective (unitOn (R := K)) := by
  intro u v h
  apply Units.ext
  have h1 := congrArg (fun w : (Γ(Sp K, ⊤))ˣ =>
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (w : Γ(Sp K, ⊤))) h
  simpa [unitOn] using h1
end ReciprocityTheory.ChartRestriction.G.H1
