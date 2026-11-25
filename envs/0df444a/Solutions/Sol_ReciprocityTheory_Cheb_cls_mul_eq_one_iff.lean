-- Prove2me | solution 1 for ReciprocityTheory.Cheb.cls_mul_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:55:37.469625+00:00
-- url     : https://prove2.me/submissions/67096cc0-24d0-4add-b46f-483598ca0e14

import Definitions.Def_ReciprocityTheory_Chebotarev_UnitPart
import Definitions.Def_ReciprocityTheory_Chebotarev_DiscreteTopologyLatOf
import Definitions.Def_ReciprocityTheory_Chebotarev_IdealLat
import Theorems.Thm_ReciprocityTheory_Cheb_nzIdeal_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (a b : NZIdeal E) :
    cls a * cls b = 1 ↔ Submodule.IsPrincipal (a.1 * b.1) := by
  have hab : a.1 * b.1 ∈ nonZeroDivisors (Ideal (𝓞 E)) :=
    mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (nzIdeal_ne_zero a) (nzIdeal_ne_zero b))
  rw [← ClassGroup.mk0_eq_one_iff hab]
  unfold cls
  rw [← map_mul]
  rfl
end ReciprocityTheory.Cheb
