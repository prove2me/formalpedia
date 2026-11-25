-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.length_eq_range_add_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:27.021951+00:00
-- url     : https://prove2.me/submissions/13572aea-3778-465e-8fd9-b229c909fb95

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_eq_ker_add_range

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
theorem _root_.solution {A : Type*} [Ring A] {L M N : Type*}
    [AddCommGroup L] [Module A L] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] {ψ : L →ₗ[A] M} {φ : M →ₗ[A] N} (h : Function.Exact ψ φ) :
    length A M = length A (LinearMap.range ψ) + length A (LinearMap.range φ) := by
  rw [length_eq_ker_add_range φ, h.linearMap_ker_eq]
end ReciprocityTheory.ChartRestriction.G.AI
