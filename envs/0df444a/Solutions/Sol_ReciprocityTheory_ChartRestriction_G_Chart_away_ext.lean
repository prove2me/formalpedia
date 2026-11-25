-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.away_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:53:47.749175+00:00
-- url     : https://prove2.me/submissions/80374a52-b14a-4d45-9353-02ff90f7bfe8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ScalePowMono
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PairCompat

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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {S : Type} [CommRing S] (u : S) {B : Type} [CommRing B] [Algebra S B]
    (f g : Localization.Away u →ₐ[S] B) : f = g := by
  first
  | exact Subsingleton.elim f g
  | exact (IsLocalization.algHom_subsingleton (Submonoid.powers u)).elim f g
  | exact AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext (Submonoid.powers u)
      (by ext x; simp))
end ReciprocityTheory.ChartRestriction.G.Chart
