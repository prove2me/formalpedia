-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.act_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:54:47.228923+00:00
-- url     : https://prove2.me/submissions/b2278a5c-2d75-45f6-838b-a6ec1c29d194

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_padd_eq_mul
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_act_zero__09a1d8b138bd

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
theorem _root_.solution (ra : Out.RingAct A O) : ∀ n : ℕ, ra.act (n : O) = (𝟙 A) ^ n
  | 0 => by rw [Nat.cast_zero, act_zero', pow_zero]
  | n + 1 => by rw [Nat.cast_succ, ra.map_add, padd_eq_mul, solution ra n, ra.map_one, pow_succ]
end ReciprocityTheory.ChartRestriction.G.DVR
