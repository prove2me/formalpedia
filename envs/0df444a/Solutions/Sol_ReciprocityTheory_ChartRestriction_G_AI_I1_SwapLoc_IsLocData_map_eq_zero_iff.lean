-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData.map_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:13.833583+00:00
-- url     : https://prove2.me/submissions/b811eec6-ee2f-47b5-8a48-374d1b57e69e

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
variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A] {S : Submonoid R}
  {V Z : Ideal R} [Z.IsPrime]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
namespace IsLocData
theorem _root_.solution [hV : V.IsPrime] (h : IsLocData R A Z.primeCompl V)
    (hVZ : V ≤ Z) (r : R) : algebraMap R A r = 0 ↔ r ∈ V := by
  constructor
  · intro h0
    obtain ⟨s, hs, hsr⟩ := h.2.2.1 r h0
    rcases hV.mem_or_mem hsr with h1 | h1
    · exact absurd (hVZ h1) hs
    · exact h1
  · exact h.2.2.2 r
end IsLocData
end ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
