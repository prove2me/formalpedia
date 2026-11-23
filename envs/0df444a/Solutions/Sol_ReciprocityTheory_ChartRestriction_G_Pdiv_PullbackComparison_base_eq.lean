-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.base_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:01.265827+00:00
-- url     : https://prove2.me/submissions/443fecd1-22b2-4e4f-988a-bdef7408e533

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_AdelicGL2ExtOfLocalComponents
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer

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
open AlgebraicGeometry CategoryTheory Limits Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
variable {X Y Z Y' : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
theorem _root_.solution {A B B' C : Scheme.{0}} {f : A ⟶ B} {g : A ⟶ B'} {f' : B ⟶ C} {g' : B' ⟶ C}
    (h : f ≫ f' = g ≫ g') (z : A) :
    f'.base (f.base z) = g'.base (g.base z) := by
  first
  | exact congrArg (fun φ : A ⟶ C => φ.base z) h
  | simpa using congrArg (fun φ : A ⟶ C => φ.base z) h
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
