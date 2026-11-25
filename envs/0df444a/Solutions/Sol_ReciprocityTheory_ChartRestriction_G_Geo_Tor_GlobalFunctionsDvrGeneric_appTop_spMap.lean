-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrGeneric.appTop_spMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:01:08.510988+00:00
-- url     : https://prove2.me/submissions/7043587c-da56-400a-9543-2cadb2ca850f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobalFunctionsDvrOpen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobalFunctionsDvrGeneric

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrGeneric
open ReciprocityTheory.ChartRestriction.G.Out
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrGeneric
theorem _root_.solution (v : V) :
    (spMap (algebraMap V (FractionRing V))).appTop ((Scheme.ΓSpecIso (CommRingCat.of V)).inv v) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv (algebraMap V (FractionRing V) v) := by
  have h := AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V)))
  have h2 := congrArg (fun g => g.hom v) h
  first
  | exact h2.symm
  | simp
  | simpa using h2.symm
end ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrGeneric
