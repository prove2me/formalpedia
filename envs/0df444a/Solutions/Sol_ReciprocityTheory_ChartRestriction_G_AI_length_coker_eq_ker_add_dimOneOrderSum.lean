-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.length_coker_eq_ker_add_dimOneOrderSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:50.527089+00:00
-- url     : https://prove2.me/submissions/5fd13440-b0a8-4ec6-839f-db2623ec56f0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_quot_prime_ne_top_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_ne_top_iff_support
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_support_coker
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_locLen_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_locLen_eq_zero_of_notMem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_locLen_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_finsum_dimOne_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_support_of_equiv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_coker_equiv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_coker_quot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_ker_quot_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_enat_step
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_euler_finLength
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_euler_ses


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module PrimeSpectrum
open scoped Pointwise
universe u v
variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution (hdim : ringKrullDim A = 1) (x : A) (M : Type v) [AddCommGroup M] [Module A M]
    [Module.Finite A M] :
    (∀ p ∈ support A M, x ∈ p.asIdeal → p.asIdeal.IsMaximal) →
      length A (LinearMap.ker (LinearMap.lsmul A M x)) ≠ ⊤ ∧
      length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) =
        length A (LinearMap.ker (LinearMap.lsmul A M x)) + dimOneSum M x := by
  have hc : ∀ (N : Type v) [AddCommGroup N] [Module A N] [Module.Finite A N],
      (∀ p ∈ support A N, x ∈ p.asIdeal → p.asIdeal.IsMaximal) →
      length A (N ⧸ LinearMap.range (LinearMap.lsmul A N x)) ≠ ⊤ := by
    intro N _ _ _ H
    rw [length_ne_top_iff_support, support_coker]
    rintro p ⟨hp, hx⟩
    exact H p hp (by simpa [mem_zeroLocus] using hx)
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime (A := A) ‹_›
    (motive := fun N _ _ _ => (∀ p ∈ support A N, x ∈ p.asIdeal → p.asIdeal.IsMaximal) →
      length A (LinearMap.ker (LinearMap.lsmul A N x)) ≠ ⊤ ∧
      length A (N ⧸ LinearMap.range (LinearMap.lsmul A N x)) =
        length A (LinearMap.ker (LinearMap.lsmul A N x)) + dimOneSum N x) ?_ ?_ ?_
  · intro N _ _ _ _ _
    have h0 : dimOneSum N x = 0 := by
      rw [dimOneSum, finsum_dimOne_eq hdim]
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [locLen_eq_zero_of_notMem p (by simp [Module.support_eq_empty]), zero_mul]
    simp [h0, Module.length_eq_zero]
  · intro N _ _ _ q e H
    have hsupp := support_of_equiv q e
    by_cases hq : q.asIdeal.IsMaximal
    · have hN : length A N ≠ ⊤ := by
        rw [e.length_eq]; exact (length_quot_prime_ne_top_iff q.asIdeal).mpr hq
      have h0 : dimOneSum N x = 0 := by
        rw [dimOneSum, finsum_dimOne_eq hdim]
        refine Finset.sum_eq_zero fun p hp => ?_
        rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, dim_quot_eq_one_iff hdim] at hp
        rw [locLen_eq_zero_of_notMem p, zero_mul]
        intro hp'
        rw [hsupp, mem_zeroLocus, SetLike.coe_subset_coe] at hp'
        exact hp (by rw [← hq.eq_of_le p.isPrime.ne_top hp']; exact hq)
      refine ⟨ne_top_of_le_ne_top hN (Module.length_le_of_injective _ (Submodule.injective_subtype _)), ?_⟩
      rw [euler_finLength hN x, h0, add_zero]
    · have hx : x ∉ q.asIdeal := fun hx => hq (H q (by rw [hsupp]; simp) hx)
      have hs : dimOneSum N x = ordMod q x := by
        rw [dimOneSum, finsum_dimOne_eq hdim, Finset.sum_eq_single q, locLen_self q e, one_mul]
        · intro p hp hpq
          rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, dim_quot_eq_one_iff hdim] at hp
          rw [locLen_eq_zero_of_notMem p, zero_mul]
          intro hp'
          rw [hsupp, mem_zeroLocus, SetLike.coe_subset_coe] at hp'
          exact hpq (PrimeSpectrum.ext (eq_of_not_max_of_le hdim hp hp'))
        · intro hq'
          exact absurd (by rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, dim_quot_eq_one_iff hdim]; exact hq) hq'
      rw [length_ker_quot_eq_zero q e hx, hs, length_coker_equiv e x, length_coker_quot, zero_add]
      exact ⟨by simp, rfl⟩
  · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hex h1 h3 H
    have H1 : ∀ p ∈ support A N₁, x ∈ p.asIdeal → p.asIdeal.IsMaximal := fun p hp =>
      H p (Module.support_subset_of_injective f hf hp)
    have H3 : ∀ p ∈ support A N₃, x ∈ p.asIdeal → p.asIdeal.IsMaximal := fun p hp =>
      H p (Module.support_subset_of_surjective g hg hp)
    obtain ⟨k1, e1⟩ := h1 H1
    obtain ⟨k3, e3⟩ := h3 H3
    have hs : dimOneSum N₂ x = dimOneSum N₁ x + dimOneSum N₃ x := by
      simp only [dimOneSum, finsum_dimOne_eq hdim, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [locLen_add f g hf hg hex p, add_mul]
    rw [hs]
    exact enat_step k1 k3 (hc N₁ H1) (hc N₃ H3) (hc N₂ H) e1 e3 (euler_ses f g hf hg hex x)
end ReciprocityTheory.ChartRestriction.G.AI
