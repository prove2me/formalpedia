-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.isGrpPullback
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:21.359912+00:00
-- url     : https://prove2.me/submissions/27bdd70f-8c14-4fb4-927e-377367a36dcc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StSiegPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_AdelicGL2ExtOfLocalComponents
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_pullback_map_left_fst__894f6221002c
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
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]
private theorem mul_left_pphi_lemma_2 :
    (MonObj.mul : (Over.pullback f).obj G ⊗ (Over.pullback f).obj G ⟶ (Over.pullback f).obj G).left ≫ pφ f G =
      pφ₂ f G ≫ (MonObj.mul : G ⊗ G ⟶ G).left := by
  rw [Functor.obj.μ_def, Over.comp_left, Category.assoc, show pφ f G = pullback.fst G.hom f from rfl,
    pullback_map_left_fst', pφ₂, Category.assoc]
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
theorem _root_.solution : IsGrpPullback ((Over.pullback f).obj G) G f (pφ f G) := by
  refine ⟨IsPullback.of_hasPullback G.hom f, ?_⟩
  intro T x y x₀ y₀ hx hy
  have hl : (lift x₀ y₀).left = (lift x y).left ≫ pφ₂ f G := by
    apply adelic_GL2_ext_of_local_components
    · have e1 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst x₀ y₀)
      have e2 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_fst x y)
      rw [Over.comp_left] at e1 e2
      rw [e1, Category.assoc, pφ₂_fst, reassoc_of% e2, hx]
    · have e1 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd x₀ y₀)
      have e2 := congrArg Over.Hom.left (CartesianMonoidalCategory.lift_snd x y)
      rw [Over.comp_left] at e1 e2
      rw [e1, Category.assoc, pφ₂_snd, reassoc_of% e2, hy]
  rw [Hom.mul_def, Hom.mul_def, Over.comp_left, Over.comp_left, Category.assoc, mul_left_pphi_lemma_2 f G,
    ← Category.assoc, ← hl]
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
