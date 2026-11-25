-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.unit_of_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:30:31.895972+00:00
-- url     : https://prove2.me/submissions/2e84caa1-827f-41e6-9bb5-e37ad4d26a94

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ScalePowMono

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
variable {S : Type} [CommRing S]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {B B' : Type} [CommRing B] [Algebra S B] [CommRing B'] [Algebra S B'] [Algebra B B']
    [IsScalarTower S B B'] {u : S} (h : IsUnit (algebraMap S B u)) : IsUnit (algebraMap S B' u) := by
  rw [IsScalarTower.algebraMap_apply S B B']
  exact h.map _
end ReciprocityTheory.ChartRestriction.G.Chart
