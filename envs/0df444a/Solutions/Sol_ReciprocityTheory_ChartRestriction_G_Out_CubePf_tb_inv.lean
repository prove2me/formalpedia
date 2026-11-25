-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.CubePf.tb_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:00:31.170711+00:00
-- url     : https://prove2.me/submissions/22593276-1bb8-4729-96cf-dbe996526437

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeMapOfThirdFaceEqPushPtLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_tb_pzero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_tb_padd

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
theorem _root_.solution {T : Over S'} (y : T ⟶ G') : tb m (y ≫ ι[G']) = tb m y ≫ ι[G] := by
  have hm : ∀ {T0 : Over S} (a b : T0 ⟶ G), padd G a b = pzero G T0 → b = a ≫ ι[G] := by
    intro T0 a b hab
    have h1 : (a ≫ ι[G]) * a = 1 := by
      change lift (a ≫ ι[G]) a ≫ μ = toUnit _ ≫ η
      simp
    have h2 : a * b = 1 := by
      change lift a b ≫ μ = toUnit _ ≫ η
      exact hab
    exact (left_inv_eq_right_inv h1 h2).symm
  apply hm
  rw [← tb_padd, ← tb_pzero]
  congr 1
  simp [padd, pzero]
end ReciprocityTheory.ChartRestriction.G.Out.CubePf
