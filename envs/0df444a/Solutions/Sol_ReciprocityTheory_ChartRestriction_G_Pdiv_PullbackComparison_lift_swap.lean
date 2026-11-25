-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.lift_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:24:25.204165+00:00
-- url     : https://prove2.me/submissions/c50d8271-19f8-4659-86ff-085ebf973a4a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StSiegPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_AdelicGL2ExtOfLocalComponents
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_p___fst_2b7b225f1a58
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_p___snd_39b6d2e321d1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_adelic_GL2_ext_of_local_components

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
theorem _root_.solution :
    (lift (snd ((Over.pullback f).obj G) ((Over.pullback f).obj G))
      (fst ((Over.pullback f).obj G) ((Over.pullback f).obj G))).left ≫ pφ₂ f G =
      pφ₂ f G ≫ (lift (snd G G) (fst G G)).left := by
  apply adelic_GL2_ext_of_local_components
  · have e1 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst (snd ((Over.pullback f).obj G) ((Over.pullback f).obj G)) (fst ((Over.pullback f).obj G) ((Over.pullback f).obj G)))
    have e2 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst (snd G G) (fst G G))
    rw [Over.comp_left] at e1 e2
    rw [Category.assoc, pφ₂_fst, reassoc_of% e1, Category.assoc, e2]
    rw [pφ₂_snd]
  · have e1 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd (snd ((Over.pullback f).obj G) ((Over.pullback f).obj G)) (fst ((Over.pullback f).obj G) ((Over.pullback f).obj G)))
    have e2 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd (snd G G) (fst G G))
    rw [Over.comp_left] at e1 e2
    rw [Category.assoc, pφ₂_snd, reassoc_of% e1, Category.assoc, e2]
    rw [pφ₂_fst]
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
