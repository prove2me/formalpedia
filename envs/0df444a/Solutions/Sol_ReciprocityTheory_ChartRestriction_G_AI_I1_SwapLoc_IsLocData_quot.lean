-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData.quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:52.733885+00:00
-- url     : https://prove2.me/submissions/9f592b87-bd99-4661-bc77-c694a8f17708

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
open ReciprocityTheory.ChartRestriction.G.AI
variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] {S : Submonoid R} {V : Ideal R}
namespace ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
namespace IsLocData
theorem _root_.solution (h : IsLocData R T S V) (P : Ideal T) :
    IsLocData R (T ⧸ P) S (P.comap (algebraMap R T)) := by
  refine ⟨fun s hs => (h.1 s hs).map (Ideal.Quotient.mk P), fun y => ?_, fun r hr => ?_, fun v hv => ?_⟩
  · obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, s, hs, hrs⟩ := h.2.1 y'
    refine ⟨r, s, hs, ?_⟩
    rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, hrs, map_mul]
  · refine ⟨1, S.one_mem, ?_⟩
    rw [one_mul, Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_algebraMap]
    exact hr
  · rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
    exact hv
end IsLocData
end ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
