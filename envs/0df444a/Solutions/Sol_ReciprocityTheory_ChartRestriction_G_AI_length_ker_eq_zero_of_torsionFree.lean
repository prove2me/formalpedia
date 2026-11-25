-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.length_ker_eq_zero_of_torsionFree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:27:54.564095+00:00
-- url     : https://prove2.me/submissions/10f5a364-0931-4ece-9412-03f385285eda

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KrullDimQuotientEqOneIffEqBot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution (M : Type*) [AddCommGroup M] [Module A M] [Module.IsTorsionFree A M]
    {x : A} (hx : x ≠ 0) :
    length A (LinearMap.ker (LinearMap.lsmul A M x)) = 0 := by
  rw [Module.length_eq_zero_iff]
  have hreg : IsSMulRegular M x := IsSMulRegular.of_ne_zero hx
  have hker : LinearMap.ker (LinearMap.lsmul A M x) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (fun a b hab => hreg (by simpa using hab))
  rw [hker]
  infer_instance
end ReciprocityTheory.ChartRestriction.G.AI
