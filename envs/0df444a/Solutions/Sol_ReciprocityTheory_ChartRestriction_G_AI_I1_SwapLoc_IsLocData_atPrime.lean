-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData.atPrime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:54.688844+00:00
-- url     : https://prove2.me/submissions/391310f3-10a5-47b3-8f76-03ce3788990e

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
theorem _root_.solution (h : IsLocData R T S V) (P : Ideal T) [hP : P.IsPrime] :
    IsLocData R (Localization.AtPrime P) (P.comap (algebraMap R T)).primeCompl V := by
  have halg : ∀ r : R, algebraMap R (Localization.AtPrime P) r =
      algebraMap T (Localization.AtPrime P) (algebraMap R T r) :=
    fun r => IsScalarTower.algebraMap_apply R T _ r
  refine ⟨fun s hs => ?_, fun y => ?_, fun r hr => ?_, fun v hv => ?_⟩
  · rw [halg]
    exact IsLocalization.map_units _ (⟨algebraMap R T s, hs⟩ : P.primeCompl)
  · obtain ⟨⟨x, m⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
    obtain ⟨r1, s1, hs1, h1⟩ := h.2.1 x
    obtain ⟨r2, s2, hs2, h2⟩ := h.2.1 (m : T)
    refine ⟨r1 * s2, r2 * s1, ?_, ?_⟩
    · show algebraMap R T (r2 * s1) ∉ P
      rw [map_mul, h2]
      intro hmem
      rcases Ideal.IsPrime.mem_or_mem hP hmem with hm | hm
      · rcases Ideal.IsPrime.mem_or_mem hP hm with hm | hm
        · exact m.2 hm
        · exact h.not_mem_of_isPrime hs2 hm
      · exact h.not_mem_of_isPrime hs1 hm
    · simp only [halg, map_mul, h1, h2]
      rw [← IsLocalization.mk'_spec (Localization.AtPrime P) x m]
      ring
  · rw [halg, IsLocalization.map_eq_zero_iff P.primeCompl] at hr
    obtain ⟨m, hm⟩ := hr
    obtain ⟨r', s', hs', h'⟩ := h.2.1 (m : T)
    have h0 : algebraMap R T (r' * r) = 0 := by
      rw [map_mul, h', mul_assoc, mul_comm (algebraMap R T s'), ← mul_assoc, hm, zero_mul]
    obtain ⟨s'', hs'', hV⟩ := h.2.2.1 _ h0
    refine ⟨s'' * r', ?_, by rw [mul_assoc]; exact hV⟩
    show algebraMap R T (s'' * r') ∉ P
    rw [map_mul, h']
    intro hmem
    rcases Ideal.IsPrime.mem_or_mem hP hmem with hm' | hm'
    · exact h.not_mem_of_isPrime hs'' hm'
    · rcases Ideal.IsPrime.mem_or_mem hP hm' with hm' | hm'
      · exact m.2 hm'
      · exact h.not_mem_of_isPrime hs' hm'
  · rw [halg, h.2.2.2 v hv, map_zero]
end IsLocData
end ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
