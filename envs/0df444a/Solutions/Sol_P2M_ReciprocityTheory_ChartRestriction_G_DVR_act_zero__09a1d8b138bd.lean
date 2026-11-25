-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_DVR_act_zero__09a1d8b138bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:42.443454+00:00
-- url     : https://prove2.me/submissions/5bec3d7e-447d-4226-af5c-2c7e9cd45576

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_padd_eq_mul

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T T' : Over S}
variable {M : LB A.left}
variable {O : Type} [CommRing O] [StarRing O]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (ra : Out.RingAct A O) : ra.act 0 = 1 := by
  have h := ra.map_add 0 0
  rw [_root_.add_zero, padd_eq_mul] at h
  exact (_root_.mul_eq_left.mp h.symm)
end ReciprocityTheory.ChartRestriction.G.DVR
