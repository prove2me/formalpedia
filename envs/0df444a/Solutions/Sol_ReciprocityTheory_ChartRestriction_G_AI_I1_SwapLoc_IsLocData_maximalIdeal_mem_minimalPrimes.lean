-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData.maximalIdeal_mem_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:02.369566+00:00
-- url     : https://prove2.me/submissions/c4389862-17d1-4158-8050-7f6b300de90b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_le_of_comap_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_comap_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_le_comap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_comap_maximalIdeal

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
theorem _root_.solution [IsLocalRing A]
    (h : IsLocData R A Z.primeCompl V) (hZex : ∃ p : Ideal A, p.IsPrime ∧ p.comap (algebraMap R A) = Z)
    {f t : R} (hZ : Z ∈ (V ⊔ Ideal.span {f} ⊔ Ideal.span {t}).minimalPrimes) :
    IsLocalRing.maximalIdeal A ∈
      (Ideal.span {algebraMap R A f, algebraMap R A t}).minimalPrimes := by
  have hc := h.comap_maximalIdeal hZex
  have hfZ : f ∈ Z :=
    hZ.1.2 (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)))
  have htZ : t ∈ Z := hZ.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self t))
  refine ⟨⟨inferInstance, ?_⟩, fun q ⟨hq, hqle⟩ _ => ?_⟩
  · rw [Ideal.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · show f ∈ (IsLocalRing.maximalIdeal A).comap (algebraMap R A)
      rw [hc]; exact hfZ
    · show t ∈ (IsLocalRing.maximalIdeal A).comap (algebraMap R A)
      rw [hc]; exact htZ
  · haveI := hq
    have hfq : algebraMap R A f ∈ q := hqle (Ideal.subset_span (Set.mem_insert _ _))
    have htq : algebraMap R A t ∈ q :=
      hqle (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
    have hZq : Z ≤ q.comap (algebraMap R A) :=
      hZ.2 ⟨Ideal.comap_isPrime _ _, sup_le (sup_le (h.le_comap q)
        (Ideal.span_le.mpr (by simpa using hfq))) (Ideal.span_le.mpr (by simpa using htq))⟩
        (h.comap_le q)
    exact h.le_of_comap_le (hc ▸ hZq)
end IsLocData
end ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
