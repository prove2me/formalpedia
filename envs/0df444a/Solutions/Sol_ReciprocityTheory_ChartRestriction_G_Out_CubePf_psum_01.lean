-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.CubePf.psum_01
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:16:47.536899+00:00
-- url     : https://prove2.me/submissions/b179855f-ce97-456c-b0b8-86ac5a5cb5fe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeMapOfThirdFaceEqPushPtLift

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.CubePf
open Semi
variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
  [IsCommMonObj G] (m : CubeMap G' G)
namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf
theorem _root_.solution {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] [IsCommMonObj H] {T : Over S₀}
    (x : Fin 3 → (T ⟶ H)) : psum H x {0, 1} = padd H (x 0) (x 1) := by
  first
    | exact congrArg (padd H (x 0)) (padd_pzero H (x 1))
    | (show padd H (x 0) (padd H (x 1) (pzero H T)) = _; rw [padd_pzero])
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
