-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:26.262877+00:00
-- url     : https://prove2.me/submissions/d53341aa-22ce-43b2-9e63-7849c3870539

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
theorem _root_.solution {X : Scheme.{0}} {O O' : X.Opens} (hle : O' ≤ O) (x : X) (hx : x ∈ O')
    (s : Γ(X, O)ˣ) : gU x hx (res hle s) = gU x (hle hx) s := by
  apply Units.ext
  first
  | exact congrArg (fun φ => φ.hom s.val) (X.presheaf.germ_res (homOfLE hle) x hx)
  | (simp [gU, res]; done)
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
