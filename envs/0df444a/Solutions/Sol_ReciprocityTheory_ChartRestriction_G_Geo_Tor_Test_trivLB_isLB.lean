-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.Test.trivLB_isLB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:44:32.522359+00:00
-- url     : https://prove2.me/submissions/2a347ba6-e606-4911-8910-c7eecef24a97

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TestObj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Test
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.Test
theorem _root_.solution (X : Scheme.{0}) : (trivLB X).IsLB where
  cover := by simp [trivLB]
  g_self _ := map_one _
  cocycle _ _ _ := by
    show res _ 1 * res _ 1 = res _ 1
    rw [map_one, map_one, map_one, _root_.one_mul]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor.Test
