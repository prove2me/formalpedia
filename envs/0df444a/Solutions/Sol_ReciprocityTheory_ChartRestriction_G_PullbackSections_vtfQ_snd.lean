-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.vtfQ_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:13:48.818821+00:00
-- url     : https://prove2.me/submissions/202b087c-4ffb-4fe0-ae09-55c1861953c6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdHol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdA

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) {x0 : Sp ℂ ⟶ S}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (a : Over.mk x0 ⟶ A) : (vtfQ A a).left ≫ (snd (Over.mk x0) A).left = a.left := by
  show (lift (𝟙 _) a ≫ snd (Over.mk x0) A).left = a.left
  rw [lift_snd]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
