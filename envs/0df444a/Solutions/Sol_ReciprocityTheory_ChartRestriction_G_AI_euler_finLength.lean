-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.euler_finLength
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:42:23.413294+00:00
-- url     : https://prove2.me/submissions/8ac42fd4-3b07-4288-bb3c-77167c5cdc9c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_eq_ker_add_range
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_eq_sub_add_quot

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
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (hN : length A N ≠ ⊤) (x : A) :
    length A (N ⧸ LinearMap.range (LinearMap.lsmul A N x)) =
      length A (LinearMap.ker (LinearMap.lsmul A N x)) := by
  have h1 := length_eq_ker_add_range (LinearMap.lsmul A N x)
  have h2 := length_eq_sub_add_quot (LinearMap.range (LinearMap.lsmul A N x))
  have hle : length A (LinearMap.range (LinearMap.lsmul A N x)) ≤ length A N := by
    rw [h1]
    exact le_add_self
  have hR := ne_top_of_le_ne_top hN hle
  rw [h1, add_comm] at h2
  exact (WithTop.add_left_cancel hR h2).symm
end ReciprocityTheory.ChartRestriction.G.AI
