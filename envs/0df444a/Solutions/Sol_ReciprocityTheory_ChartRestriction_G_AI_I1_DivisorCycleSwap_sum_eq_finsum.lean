-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap.sum_eq_finsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:48:34.534788+00:00
-- url     : https://prove2.me/submissions/c1645964-3d23-4139-ba51-2641b48df720

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_DivisorCycleSwap_isRelevant_of_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_DivisorCycleSwap_divCycle_apply_of_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_DivisorCycleSwap_divCycle_apply_of_not_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_DivisorCycleSwap_cast_multAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_DivisorCycleSwap_mem_minimalPrimes_sup_of_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_atPrime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_comap_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_eq_of_comap_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_height_eq_one_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_length_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_IsLocData_quot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_exists_prime_comap_atPrime_quot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_isLocData_atPrime_quot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_SwapLoc_lenAt_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
open SwapLoc
open ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap
namespace ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap
theorem _root_.solution {V Z : Ideal (MRingOver F ι)} [V.IsPrime] [hZp : Z.IsPrime]
    [(Z.map (Ideal.Quotient.mk V)).IsPrime] {f t : MRingOver F ι} (hZr : IsRelevant Z)
    (hZ : Z ∈ (V ⊔ Ideal.span {f} ⊔ Ideal.span {t}).minimalPrimes) (hfV : f ∉ V) :
    ((∑ W ∈ (divSupp_finite V f).toFinset, divCycle V f W * divCycle W t Z : ℕ) : ℕ∞) =
      ∑ᶠ (p : PrimeSpectrum (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))))
        (_ : p.asIdeal.height = 1 ∧
          algebraMap (MRingOver F ι) (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))) f ∈
            p.asIdeal),
        ordLoc p (algebraMap (MRingOver F ι) _ f) * ordMod p (algebraMap (MRingOver F ι) _ t) := by
  classical
  have hVZ : V ≤ Z := le_sup_left.trans (le_sup_left.trans hZ.1.2)
  have h := isLocData_atPrime_quot V Z hVZ
  have hex : ∀ Q : Ideal (MRingOver F ι), Q.IsPrime → V ≤ Q → Q ≤ Z →
      ∃ p : Ideal (Localization.AtPrime (Z.map (Ideal.Quotient.mk V))), p.IsPrime ∧
        p.comap (algebraMap (MRingOver F ι) _) = Q :=
    fun Q hQ hVQ hQZ => exists_prime_comap_atPrime_quot V Z Q hQ hVQ hQZ
  have hterm : ∀ W ∈ (divSupp_finite V f).toFinset, divCycle V f W * divCycle W t Z =
      if W ≤ Z then multAt (V ⊔ Ideal.span {f}) W * multAt (W ⊔ Ideal.span {t}) Z else 0 := by
    intro W hW
    rw [Set.Finite.mem_toFinset] at hW
    rw [divCycle_apply_of_mem hW]
    split_ifs with hWZ
    · rw [divCycle_apply_of_mem ⟨mem_minimalPrimes_sup_of_le hZ hW.1 hWZ, hZr⟩]
    · rw [divCycle_apply_of_not_mem (fun h' => hWZ (le_sup_left.trans h'.1.1.2)), mul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  push_cast
  rw [← finsum_mem_coe_finset]
  symm
  refine finsum_mem_eq_of_bijOn (fun p => p.asIdeal.comap (algebraMap (MRingOver F ι) _))
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
    rw [cast_multAt hm, cast_multAt (mem_minimalPrimes_sup_of_le hZ hm hle), lenAt_eq, lenAt_eq,
      (h.atPrime p.asIdeal).length_eq f, (h.quot p.asIdeal).length_eq t, ordLoc, ordMod,
      ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (MRingOver F ι) (Localization.AtPrime (Z.map (Ideal.Quotient.mk V)))
        (Localization.AtPrime (Z.map (Ideal.Quotient.mk V)) ⧸ p.asIdeal),
      Ideal.Quotient.algebraMap_eq]
end ReciprocityTheory.ChartRestriction.G.AI.I1.DivisorCycleSwap
