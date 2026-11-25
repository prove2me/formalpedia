-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.eq_unit_mul_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:35:06.73585+00:00
-- url     : https://prove2.me/submissions/74482d8b-0e88-4320-a048-bf4afdade109

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_RegDom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Theorems.Thm_ReciprocityTheory_AnForm_R_exists_le_associated_of_dvd_prod_primes
import Theorems.Thm_ReciprocityTheory_AnForm_R_prime_of_regular_params

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open IsLocalRing
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution [IsRegularLocalRing R] {n : ℕ} (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = maximalIdeal R) (hdim : (n : WithBot ℕ∞) = ringKrullDim R)
    (J : Finset (Fin n)) {x : R} (hx0 : x ≠ 0) (hrad : (∏ i ∈ J, f i) ∈ (Ideal.span {x}).radical) :
    ∃ (u : Rˣ) (m : Fin n → ℕ), (∀ i, i ∉ J → m i = 0) ∧ x = u * ∏ i ∈ J, f i ^ m i := by
  obtain ⟨k, hk⟩ := hrad
  rw [Ideal.mem_span_singleton] at hk
  have hprimes : ∀ i ∈ k • J.val, Prime (f i) := fun i _ => prime_of_regular_params f hspan hdim i
  have hprod : ((k • J.val).map f).prod = (∏ i ∈ J, f i) ^ k := by
    rw [Multiset.map_nsmul, Multiset.prod_nsmul]
    rfl
  rw [← hprod] at hk
  obtain ⟨t, ht, hxt⟩ := exists_le_associated_of_dvd_prod_primes f (k • J.val) hprimes hk
  have htJ : ∀ i, i ∉ J → Multiset.count i t = 0 := fun i hi => Multiset.count_eq_zero.2 fun hit =>
    hi (Multiset.mem_of_mem_nsmul (Multiset.mem_of_le ht hit))
  obtain ⟨u, hu⟩ := hxt.symm
  refine ⟨u, fun i => Multiset.count i t, htJ, ?_⟩
  rw [← hu, Finset.prod_multiset_map_count, mul_comm]
  congr 1
  apply Finset.prod_subset
  · intro i hi
    by_contra hiJ
    exact Multiset.count_ne_zero.2 (Multiset.mem_toFinset.1 hi) (htJ i hiJ)
  · intro i _ hi
    rw [Multiset.count_eq_zero.2 (fun h => hi (Multiset.mem_toFinset.2 h)), pow_zero]
end ReciprocityTheory.AnForm.R
