-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.length_quot_ne_top_of_mem_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:15.400289+00:00
-- url     : https://prove2.me/submissions/ab4ef419-8bde-424d-be80-d28c6ff986a3

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
namespace ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
theorem _root_.solution {A : Type*} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (I : Ideal A) (hm : IsLocalRing.maximalIdeal A ∈ I.minimalPrimes) :
    Module.length A (A ⧸ I) ≠ ⊤ := by
  haveI := IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hm
  rw [Module.length_eq_of_surjective (S := A) (R := A ⧸ I) (M := A ⧸ I)
    (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)]
  exact Module.length_ne_top
end ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
