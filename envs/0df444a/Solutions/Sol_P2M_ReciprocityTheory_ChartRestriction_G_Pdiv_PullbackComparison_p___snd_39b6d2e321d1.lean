-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_p___snd_39b6d2e321d1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:20.130408+00:00
-- url     : https://prove2.me/submissions/1b36fa43-4fd8-47d3-9f68-561e1b4e4bc3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StSiegPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_AdelicGL2ExtOfLocalComponents
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_pullback_map_left_fst__894f6221002c

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
theorem _root_.solution : pφ₂ f G ≫ (snd G G).left = (snd ((Over.pullback f).obj G) ((Over.pullback f).obj G)).left ≫ pφ f G := by
  rw [show pφ f G = pullback.fst G.hom f from rfl, pφ₂, Category.assoc, ← pullback_map_left_fst',
    ← Category.assoc, ← Over.comp_left, Functor.Monoidal.μ_snd]
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
