-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_proof_82ad9735a6be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:05:47.197247+00:00
-- url     : https://prove2.me/submissions/46e0ee1c-b624-4e80-90a8-61d1bb5cfb1f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsLocalCoeffLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimTwoSumReading
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_length_loc_eq_ordLoc_c7fa6570f1d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_length_max_eq_ordMod_f57d7a15dfe9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_mem_minimalPrimes_iff_4ff3b0367414
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_max_mem_minimalPrimes_49103e6a00fd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_locLen_ne_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc IsLocalRing
noncomputable section
open DimTwoSumReading
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace DimTwoSumReading
theorem _root_.solution : DimTwoSumReading.Statement := by
  intro A _ _ _ _ h2 a b ha hab
  classical
  have hT : {p : PrimeSpectrum A | p.asIdeal.height = 1 ∧ a ∈ p.asIdeal}.Finite :=
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {a})).preimage
      (fun p _ q _ h => PrimeSpectrum.ext h)).subset
      (fun p hp => (mem_minimalPrimes_iff ha p.asIdeal).mpr hp)
  have key : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 ∧ a ∈ p.asIdeal →
      (locCycle (Ideal.span {a}) p.asIdeal = ((ordLoc p a).toNat : ℤ) ∧ ordLoc p a ≠ ⊤) ∧
      (locCycle (p.asIdeal ⊔ Ideal.span {b}) (maximalIdeal A) = ((ordMod p b).toNat : ℤ) ∧
        ordMod p b ≠ ⊤) := by
    intro p hp
    have hmin := (mem_minimalPrimes_iff ha p.asIdeal).mpr hp
    have hlA := length_loc_eq_ordLoc p.asIdeal a
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · unfold locCycle; rw [dif_pos hmin]; exact congrArg (fun x : ℕ∞ => (x.toNat : ℤ)) hlA
    · rw [← hlA]; exact ReciprocityTheory.ChartRestriction.G.AI.I1.locLen_ne_top hmin
    by_cases hbm : b ∈ maximalIdeal A
    · have hmm := max_mem_minimalPrimes h2 p.asIdeal hp.1 (hab _ p.isPrime hp.1 hp.2) hbm
      have hlB := length_max_eq_ordMod p.asIdeal b
      refine ⟨?_, ?_⟩
      · unfold locCycle; rw [dif_pos hmm]; exact congrArg (fun x : ℕ∞ => (x.toNat : ℤ)) hlB
      · rw [← hlB]; exact ReciprocityTheory.ChartRestriction.G.AI.I1.locLen_ne_top hmm
    · have h0 : ordMod p b = 0 := Ring.ord_of_isUnit ((notMem_maximalIdeal.mp hbm).map _)
      have hnm : maximalIdeal A ∉ (p.asIdeal ⊔ Ideal.span {b}).minimalPrimes := fun h =>
        hbm (h.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl)))
      rw [h0]
      refine ⟨?_, ENat.zero_ne_top⟩
      unfold locCycle; rw [dif_neg hnm]; rfl
  have hsupp : Function.support (fun W : Ideal A => locCycle (Ideal.span {a}) W *
      locCycle (W ⊔ Ideal.span {b}) (maximalIdeal A)) ⊆
      (hT.toFinset.map ⟨PrimeSpectrum.asIdeal, by intro p q h; exact PrimeSpectrum.ext h⟩ : Finset (Ideal A)) := by
    intro W hW
    have hne : locCycle (Ideal.span {a}) W ≠ 0 := left_ne_zero_of_mul hW
    have hmin : W ∈ (Ideal.span {a}).minimalPrimes := by
      by_contra h
      exact hne (by unfold locCycle; rw [dif_neg h])
    have := hmin.1.1
    rw [Finset.coe_map, Set.Finite.coe_toFinset]
    exact ⟨⟨W, hmin.1.1⟩, (mem_minimalPrimes_iff ha W).mp hmin, rfl⟩
  refine ⟨∑ p ∈ hT.toFinset, (ordLoc p a).toNat * (ordMod p b).toNat, ?_, ?_⟩
  · rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_map]
    push_cast
    refine Finset.sum_congr rfl fun p hp => ?_
    have hk := key p (hT.mem_toFinset.mp hp)
    show locCycle (Ideal.span {a}) p.asIdeal * locCycle (p.asIdeal ⊔ Ideal.span {b}) (maximalIdeal A) = _
    rw [hk.1.1, hk.2.1]
  · refine (finsum_mem_eq_finite_toFinset_sum (fun p => ordLoc p a * ordMod p b) hT).trans ?_
    push_cast
    refine Finset.sum_congr rfl fun p hp => ?_
    have hk := key p (hT.mem_toFinset.mp hp)
    rw [ENat.natCast_toNat hk.1.2, ENat.natCast_toNat hk.2.2]
end DimTwoSumReading
end GroundTheory.Heights₂.Heights.NumbersDVR
