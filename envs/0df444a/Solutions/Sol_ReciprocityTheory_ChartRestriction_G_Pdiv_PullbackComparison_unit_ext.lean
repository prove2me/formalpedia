-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.unit_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:26.299795+00:00
-- url     : https://prove2.me/submissions/a035809c-47f8-46ce-8984-52cfad493fe6

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
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
theorem _root_.solution {X : Scheme.{0}} {O : X.Opens} (s t : Γ(X, O)ˣ)
    (h : ∀ x (hx : x ∈ O), gU x hx s = gU x hx t) : s = t := by
  apply Units.ext
  apply TopCat.Presheaf.section_ext X.sheaf
  intro x hx
  first
  | exact congrArg Units.val (h x hx)
  | simpa [gU] using congrArg Units.val (h x hx)
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
