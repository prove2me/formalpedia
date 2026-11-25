-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.dimOneFormula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:58:39.352655+00:00
-- url     : https://prove2.me/submissions/b8dfdb7a-b878-4bd6-9e0e-a0933f73504b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_ne_top_iff_support
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_support_coker
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_coker_eq_ker_add_dimOneOrderSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module PrimeSpectrum
open scoped Pointwise
universe u v
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution : LocalLengthAdditivity := by
  unfold LocalLengthAdditivity
  intro A _ _ _ M _ _ _ x hdim hfin
  have h := (length_ne_top_iff_support (M ⧸ LinearMap.range (LinearMap.lsmul A M x))).1 hfin
  rw [support_coker] at h
  exact length_coker_eq_ker_add_dimOneOrderSum hdim x M (fun p hp hx =>
    h p ⟨hp, (PrimeSpectrum.mem_zeroLocus _ _).2 (Set.singleton_subset_iff.2 hx)⟩)
end ReciprocityTheory.ChartRestriction.G.AI
