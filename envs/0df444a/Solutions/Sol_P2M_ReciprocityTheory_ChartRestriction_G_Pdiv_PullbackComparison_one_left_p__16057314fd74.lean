-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_one_left_p__16057314fd74
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:45.848614+00:00
-- url     : https://prove2.me/submissions/289424a8-9769-4721-b2b8-c8e6cf09f7b8

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
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]
private theorem unit_left_ext_lemma {Z : Scheme.{0}} (u v : Z ⟶ (𝟙_ (Over S)).left)
    (h : u ≫ (𝟙_ (Over S)).hom = v ≫ (𝟙_ (Over S)).hom) : u = v := by
  have key : (Over.homMk u : Over.mk (u ≫ (𝟙_ (Over S)).hom) ⟶ 𝟙_ (Over S)) = Over.homMk v h.symm :=
    CartesianMonoidalCategory.toUnit_unique _ _
  exact congrArg Over.Hom.left key
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
theorem _root_.solution :
    (1 : (Over.pullback f).obj G ⟶ (Over.pullback f).obj G).left ≫ pφ f G =
      pφ f G ≫ (1 : G ⟶ G).left := by
  have e : (toUnit ((Over.pullback f).obj G)).left ≫ (Functor.LaxMonoidal.ε (Over.pullback f)).left ≫
      pullback.snd (𝟙_ (Over S)).hom f = pullback.snd G.hom f := by
    have h0 := Over.w (toUnit ((Over.pullback f).obj G) ≫ Functor.LaxMonoidal.ε (Over.pullback f))
    rw [Over.comp_left, Category.assoc] at h0
    exact h0
  have hε : (toUnit ((Over.pullback f).obj G)).left ≫ (Functor.LaxMonoidal.ε (Over.pullback f)).left ≫
      pullback.fst (𝟙_ (Over S)).hom f = pullback.fst G.hom f ≫ (toUnit G).left := by
    apply unit_left_ext_lemma
    simp only [Category.assoc]
    rw [pullback.condition, reassoc_of% e, Over.w, pullback.condition]
  rw [Hom.one_def, Hom.one_def, Functor.obj.η_def]
  simp only [Over.comp_left, Category.assoc]
  rw [show pφ f G = pullback.fst G.hom f from rfl, pullback_map_left_fst', reassoc_of% hε]
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
