-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_sum_eq_finsum_ad49380098f7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:15:34.15295+00:00
-- url     : https://prove2.me/submissions/14efd7b8-e49b-42d9-b42a-d4ba9bd0b949

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwapCyclesArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NotRelevantOfDimZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSwapCycles
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_mem_minimalPrimes_sup_0626960bf546
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_isRelevant_of_le_9723e06f73a7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_divCycle_of_mem_90dbb309e064
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_divCycle_of_not_mem_e510c3578bb2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SwapCyclesAlt_cast_multAt_e7f6e9977867
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_DivisorCycleSwap_cast_multAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_DivisorCycleSwap_isRelevant_of_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_atPrime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_comap_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_eq_of_comap_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_height_eq_one_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_length_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_quot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_lenAt_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
  ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.SwapCyclesAlt
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.SwapCyclesAlt
theorem _root_.solution {V Z : Ideal (MRing ι)} [V.IsPrime] [Z.IsPrime] {A : Type} [CommRing A]
    [IsDomain A] [IsNoetherianRing A] [Algebra (MRing ι) A]
    (h : IsLocData (MRing ι) A Z.primeCompl V) (hVZ : V ≤ Z)
    (hex : ∀ Q : Ideal (MRing ι), Q.IsPrime → V ≤ Q → Q ≤ Z →
      ∃ p : Ideal A, p.IsPrime ∧ p.comap (algebraMap (MRing ι) A) = Q)
    {f t : MRing ι} (hZr : IsRelevant Z)
    (hZ : Z ∈ (V ⊔ Ideal.span {f} ⊔ Ideal.span {t}).minimalPrimes) (hfV : f ∉ V) :
    ((∑ W ∈ (divSupp_finite V f).toFinset, divCycle V f W * divCycle W t Z : ℕ) : ℕ∞) =
      ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ algebraMap (MRing ι) A f ∈ p.asIdeal),
        ordLoc p (algebraMap (MRing ι) A f) * ordMod p (algebraMap (MRing ι) A t) := by
  classical
  have hterm : ∀ W ∈ (divSupp_finite V f).toFinset, divCycle V f W * divCycle W t Z =
      if W ≤ Z then multAt (V ⊔ Ideal.span {f}) W * multAt (W ⊔ Ideal.span {t}) Z else 0 := by
    intro W hW
    rw [Set.Finite.mem_toFinset] at hW
    rw [divCycle_of_mem hW]
    split_ifs with hWZ
    · rw [divCycle_of_mem ⟨mem_minimalPrimes_sup hZ hW.1 hWZ, hZr⟩]
    · rw [divCycle_of_not_mem (fun h' => hWZ (le_sup_left.trans h'.1.1.2)), mul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  push_cast
  rw [← finsum_mem_coe_finset]
  symm
  refine finsum_mem_eq_of_bijOn (fun p => p.asIdeal.comap (algebraMap (MRing ι) A))
    ⟨?_, ?_, ?_⟩ ?_
  · intro p hp
    have hm := (h.height_eq_one_iff hVZ hex hfV p.asIdeal).mp hp
    have hle := h.comap_le p.asIdeal
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨⟨hm, isRelevant_of_le hZr hle⟩, hle⟩
  · intro p _ p' _ e
    exact PrimeSpectrum.ext (h.eq_of_comap_eq e)
  · intro W hW
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hW
    obtain ⟨p, hp, hpW⟩ := hex W hW.1.1.1.1 (le_sup_left.trans hW.1.1.1.2) hW.2
    haveI := hp
    exact ⟨⟨p, hp⟩, (h.height_eq_one_iff hVZ hex hfV p).mpr (hpW ▸ hW.1.1), hpW⟩
  · intro p hp
    have hm := (h.height_eq_one_iff hVZ hex hfV p.asIdeal).mp hp
    have hle := h.comap_le p.asIdeal
    rw [cast_multAt hm, cast_multAt (mem_minimalPrimes_sup hZ hm hle), lenAt_eq, lenAt_eq,
      (h.atPrime p.asIdeal).length_eq f, (h.quot p.asIdeal).length_eq t, ordLoc, ordMod,
      ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (MRing ι) A (A ⧸ p.asIdeal),
      Ideal.Quotient.algebraMap_eq]
end GroundTheory.Heights₂.Heights.Inter.SwapCyclesAlt
