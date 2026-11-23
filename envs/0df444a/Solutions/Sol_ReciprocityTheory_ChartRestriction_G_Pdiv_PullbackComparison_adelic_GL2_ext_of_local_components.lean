-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.adelic_GL2_ext_of_local_components
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:08.838898+00:00
-- url     : https://prove2.me/submissions/f23bae0f-452c-48b7-8cdd-4d0e7e6e88c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StSiegPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_AdelicGL2ExtOfLocalComponents

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
theorem _root_.solution {R : Scheme.{0}} (a b : R ⟶ (G2 G).left)
    (h1 : a ≫ (fst G G).left = b ≫ (fst G G).left) (h2 : a ≫ (snd G G).left = b ≫ (snd G G).left) :
    a = b := by
  have hab : a ≫ (G ⊗ G).hom = b ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), reassoc_of% h1]
  have key : (Over.homMk a : Over.mk (a ≫ (G ⊗ G).hom) ⟶ G ⊗ G) = Over.homMk b hab.symm := by
    apply CartesianMonoidalCategory.hom_ext
    · ext
      simpa using h1
    · ext
      simpa using h2
  exact congrArg Over.Hom.left key
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
