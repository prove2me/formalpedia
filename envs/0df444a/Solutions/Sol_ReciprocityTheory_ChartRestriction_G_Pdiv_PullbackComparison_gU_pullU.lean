-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU_pullU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:01.703802+00:00
-- url     : https://prove2.me/submissions/3a14a247-edea-46aa-ad3e-3fcbd892f5f8

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
theorem _root_.solution {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (y : Y) (hy : y ∈ f ⁻¹ᵁ U)
    (x : Γ(X, U)ˣ) :
    gU y hy (pullU f U x) = Units.map (f.stalkMap y).hom (gU (f.base y) hy x) := by
  apply Units.ext
  first
  | (simp [gU, pullU]; done)
  | exact (congrArg (fun φ => φ.hom x.val) (Scheme.Hom.germ_stalkMap f U y hy)).symm
  | exact congrArg (fun φ => φ.hom x.val) (Scheme.Hom.germ_stalkMap f U y hy)
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
