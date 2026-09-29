-- Prove2me | solution 1 for ValuationSubring.exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/59547aaa-282f-5be1-8ac7-380d721e5be7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic

namespace TorSol

lemma exists_ne_map_eq_of_sum_eq_zero {R : Type*} [CommRing R]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)
    {ι : Type*} (s : Finset ι) (t : ι → R) (hs : s.Nonempty) (ht : ∀ i ∈ s, v (t i) ≠ 0)
    (hsum : ∑ i ∈ s, t i = 0) : ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ v (t i) = v (t j) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨i₀, hi₀, hmax⟩ := s.exists_max_image (fun i => v (t i)) hs
  have hlt : ∀ j ∈ s.erase i₀, v (t j) < v (t i₀) := by
    intro j hj
    obtain ⟨hji, hjs⟩ := Finset.mem_erase.mp hj
    exact lt_of_le_of_ne (hmax j hjs) (hcon j hjs i₀ hi₀ hji)
  have hrest : v (∑ j ∈ s.erase i₀, t j) < v (t i₀) := v.map_sum_lt (ht i₀ hi₀) hlt
  have hsplit : ∑ i ∈ s, t i = t i₀ + ∑ j ∈ s.erase i₀, t j := (Finset.add_sum_erase s t hi₀).symm
  have h : v (∑ i ∈ s, t i) = v (t i₀) := by rw [hsplit, v.map_add_eq_of_lt_left hrest]
  rw [hsum, map_zero] at h
  exact ht i₀ hi₀ h.symm

lemma exists_lt_valuation_eq {E F : Type*} [Field E] [Field F] [Algebra E F]
    (O : ValuationSubring F) {g : F} (hg : g ≠ 0) {p : Polynomial E} (hp : p ≠ 0)
    (hpg : Polynomial.aeval g p = 0) :
    ∃ i j : ℕ, i < j ∧ p.coeff i ≠ 0 ∧ p.coeff j ≠ 0 ∧
      O.valuation (algebraMap E F (p.coeff i) * g ^ i) =
        O.valuation (algebraMap E F (p.coeff j) * g ^ j) := by
  classical
  set t : ℕ → F := fun i => algebraMap E F (p.coeff i) * g ^ i with ht
  have hsum : ∑ i ∈ p.support, t i = 0 := by
    have h := hpg
    rw [Polynomial.aeval_eq_sum_range] at h

    have h' : ∑ i ∈ Finset.range (p.natDegree + 1), t i = ∑ i ∈ p.support, t i := by
      symm
      refine Finset.sum_subset (fun i hi => ?_) (fun i _ hi => ?_)
      · exact Finset.mem_range_succ_iff.mpr (Polynomial.le_natDegree_of_mem_supp i hi)
      · have h0 : p.coeff i = 0 := by simpa [Polynomial.mem_support_iff] using hi
        simp [ht, h0]
    rw [← h']
    simpa [ht, Algebra.smul_def] using h
  have hsupp : p.support.Nonempty := Polynomial.support_nonempty.mpr hp
  have htne : ∀ i ∈ p.support, O.valuation (t i) ≠ 0 := by
    intro i hi
    rw [Valuation.ne_zero_iff]
    refine mul_ne_zero ?_ (pow_ne_zero _ hg)
    exact (map_ne_zero (algebraMap E F)).mpr (Polynomial.mem_support_iff.mp hi)
  obtain ⟨i, hi, j, hj, hij, hval⟩ :=
    exists_ne_map_eq_of_sum_eq_zero O.valuation p.support t hsupp htne hsum
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact ⟨i, j, hlt, Polynomial.mem_support_iff.mp hi, Polynomial.mem_support_iff.mp hj, hval⟩
  · exact ⟨j, i, hlt, Polynomial.mem_support_iff.mp hj, Polynomial.mem_support_iff.mp hi,
      hval.symm⟩

end TorSol

open TorSol in
theorem solution
    {E F : Type*} [Field E] [Field F] [Algebra E F] [Algebra.IsAlgebraic E F]
    (O : ValuationSubring F) {g : F} (hg : g ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ c : E, c ≠ 0 ∧ O.valuation (g ^ n) = O.valuation (algebraMap E F c) := by
  obtain ⟨p, hp, hpg⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := E) g)
  obtain ⟨i, j, hij, hi, hj, hval⟩ := exists_lt_valuation_eq O hg hp hpg
  refine ⟨j - i, Nat.sub_pos_of_lt hij, p.coeff i / p.coeff j, div_ne_zero hi hj, ?_⟩
  set v := O.valuation with hv
  have hgi : v g ^ i ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff v).mpr hg)
  have haj : v (algebraMap E F (p.coeff j)) ≠ 0 :=
    (Valuation.ne_zero_iff v).mpr ((map_ne_zero (algebraMap E F)).mpr hj)
  rw [map_mul, map_mul, map_pow, map_pow] at hval

  have hsplit : v g ^ j = v g ^ i * v g ^ (j - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hij.le]
  rw [hsplit] at hval

  have hkey : v (algebraMap E F (p.coeff i)) = v (algebraMap E F (p.coeff j)) * v g ^ (j - i) := by
    have h1 : v (algebraMap E F (p.coeff i)) * v g ^ i =
        (v (algebraMap E F (p.coeff j)) * v g ^ (j - i)) * v g ^ i := by
      rw [hval, mul_assoc, mul_comm (v g ^ i) (v g ^ (j - i))]
    exact mul_right_cancel₀ hgi h1
  rw [map_pow, map_div₀ (algebraMap E F),
    map_div₀ v (algebraMap E F (p.coeff i)) (algebraMap E F (p.coeff j)), hkey,
    mul_div_cancel_left₀ _ haj]

end S_ValuationSubring_exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic
end P2MW
export P2MW.S_ValuationSubring_exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic (solution)
