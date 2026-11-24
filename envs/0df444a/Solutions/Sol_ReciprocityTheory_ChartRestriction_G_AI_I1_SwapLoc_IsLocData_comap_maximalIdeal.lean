-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData.comap_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:52.560819+00:00
-- url     : https://prove2.me/submissions/c738940e-8afd-401c-ae84-7aa5c7526ade

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_comap_le

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
theorem _root_.solution [IsLocalRing A] (h : IsLocData R A Z.primeCompl V)
    (hex : ∃ p : Ideal A, p.IsPrime ∧ p.comap (algebraMap R A) = Z) :
    (IsLocalRing.maximalIdeal A).comap (algebraMap R A) = Z := by
  obtain ⟨p, hp, hpZ⟩ := hex
  apply le_antisymm (h.comap_le _)
  rw [← hpZ]
  exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hp.ne_top)
end IsLocData
end ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
