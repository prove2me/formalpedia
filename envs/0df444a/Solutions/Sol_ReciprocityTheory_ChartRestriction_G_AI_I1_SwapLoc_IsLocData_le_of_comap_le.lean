-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData.le_of_comap_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:43:07.295611+00:00
-- url     : https://prove2.me/submissions/7d6d6ac6-c2d4-45c5-932d-c84be58a0b79

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_not_mem_of_isPrime

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
theorem _root_.solution (h : IsLocData R T S V) {P P' : Ideal T} [hP' : P'.IsPrime]
    (hle : P.comap (algebraMap R T) ≤ P'.comap (algebraMap R T)) : P ≤ P' := by
  intro y hy
  obtain ⟨r, s, hs, hrs⟩ := h.2.1 y
  have hr : r ∈ P.comap (algebraMap R T) := by
    rw [Ideal.mem_comap, hrs]
    exact P.mul_mem_right _ hy
  have hr' := hle hr
  rw [Ideal.mem_comap, hrs] at hr'
  rcases hP'.mem_or_mem hr' with h1 | h1
  · exact h1
  · exact absurd h1 (h.not_mem_of_isPrime hs)
end IsLocData
end ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
