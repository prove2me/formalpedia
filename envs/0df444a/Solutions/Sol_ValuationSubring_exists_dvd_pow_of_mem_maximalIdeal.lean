-- Prove2me | solution 1 for ValuationSubring.exists_dvd_pow_of_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/636ded52-e340-5d75-813b-fc2327d9c818

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_dvd_pow_of_mem_maximalIdeal

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Ws25
namespace Archimedean

section Archimedean

open Polynomial

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

theorem exists_ne_val_eq_of_sum_eq_zero {ι : Type*} (s : Finset ι) (t : ι → K)
    (hsum : ∑ i ∈ s, t i = 0) {i₁ : ι} (hi₁ : i₁ ∈ s) (ht₁ : t i₁ ≠ 0) :
    ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ t i ≠ 0 ∧ t j ≠ 0 ∧ v (t i) = v (t j) := by
  classical
  obtain ⟨i₀, hi₀, hmax⟩ := s.exists_max_image (fun i => v (t i)) ⟨i₁, hi₁⟩
  have hpos₁ : 0 < v (t i₁) := (Valuation.pos_iff v).mpr ht₁
  have ht₀ : t i₀ ≠ 0 := (Valuation.pos_iff v).mp (lt_of_lt_of_le hpos₁ (hmax i₁ hi₁))
  by_contra hne
  push_neg at hne
  have hlt : ∀ j ∈ s.erase i₀, v (t j) < v (t i₀) := by
    intro j hj
    obtain ⟨hji, hjs⟩ := Finset.mem_erase.mp hj
    by_cases htj : t j = 0
    · rw [htj, map_zero]; exact (Valuation.pos_iff v).mpr ht₀
    · exact lt_of_le_of_ne (hmax j hjs) fun h => hne j hjs i₀ hi₀ hji htj ht₀ h
  have h1 : v (∑ j ∈ s.erase i₀, t j) < v (t i₀) :=
    v.map_sum_lt ((Valuation.ne_zero_iff v).mpr ht₀) hlt
  have h2 : v (t i₀ + ∑ j ∈ s.erase i₀, t j) = v (t i₀) := v.map_add_eq_of_lt_left h1
  rw [Finset.add_sum_erase s t hi₀, hsum, map_zero] at h2
  exact ht₀ ((Valuation.zero_iff v).mp h2.symm)

variable (A : ValuationSubring K) {q : ℕ} [hq : Fact q.Prime]

local notation "w" => ValuationSubring.valuation A

theorem valuation_natCast_eq_one_of_not_dvd (hqA : (q : K) ∈ A.nonunits) {n : ℕ} (hn : ¬ q ∣ n) :
    w (n : K) = 1 := by
  have hcop : IsCoprime (q : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.mpr
    ((Nat.Prime.coprime_iff_not_dvd hq.out).mpr hn)
  obtain ⟨a, b, hab⟩ := hcop
  have habK : (a : K) * q + (b : K) * n = 1 := by exact_mod_cast congrArg (fun z : ℤ => (z : K)) hab
  have hq1 : w (q : K) < 1 := (A.mem_nonunits_iff).mp hqA
  have ha : w (a : K) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A a)
  have hb : w (b : K) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A b)
  have hn1 : w (n : K) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A n)
  have haq : w ((a : K) * q) < 1 := by
    rw [map_mul]
    calc w (a : K) * w (q : K) ≤ 1 * w (q : K) := mul_le_mul_left ha _
      _ < 1 := by rw [one_mul]; exact hq1

  by_contra hne
  have hnlt : w (n : K) < 1 := lt_of_le_of_ne hn1 hne
  have hbn : w ((b : K) * n) < 1 := by
    rw [map_mul]
    calc w (b : K) * w (n : K) ≤ 1 * w (n : K) := mul_le_mul_left hb _
      _ < 1 := by rw [one_mul]; exact hnlt
  have := Valuation.map_add_lt (w) haq hbn
  rw [habK, map_one] at this
  exact lt_irrefl _ this

theorem exists_valuation_natCast_eq (hqA : (q : K) ∈ A.nonunits) {n : ℕ} (hn : n ≠ 0) :
    ∃ e : ℕ, w (n : K) = w (q : K) ^ e := by
  obtain ⟨e, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn q hq.out.one_lt.ne'
  refine ⟨e, ?_⟩
  rw [Nat.cast_mul, Nat.cast_pow, map_mul, map_pow, valuation_natCast_eq_one_of_not_dvd A hqA hn',
    mul_one]

theorem exists_valuation_ratCast_eq (hqA : (q : K) ∈ A.nonunits) [CharZero K] {r : ℚ} (hr : r ≠ 0) :
    ∃ a b : ℕ, w (r : K) * w (q : K) ^ a = w (q : K) ^ b := by
  have hnum : r.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hr)
  obtain ⟨b, hb⟩ := exists_valuation_natCast_eq A hqA hnum
  obtain ⟨a, ha⟩ := exists_valuation_natCast_eq A hqA r.den_nz
  refine ⟨a, b, ?_⟩
  have hden : (r.den : K) ≠ 0 := by exact_mod_cast r.den_nz
  have hnumK : w (r.num : K) = w (r.num.natAbs : K) := by
    rcases Int.natAbs_eq r.num with h | h
    · have this : w (r.num : K) = w ((r.num.natAbs : ℤ) : K) := congrArg (fun z : ℤ => w (z : K)) h
      rwa [Int.cast_natCast] at this
    · have this : w (r.num : K) = w ((-(r.num.natAbs : ℤ) : ℤ) : K) :=
        congrArg (fun z : ℤ => w (z : K)) h
      rwa [Int.cast_neg, Int.cast_natCast, Valuation.map_neg] at this
  rw [Rat.cast_def, map_div₀, ← ha, hnumK, hb, div_mul_cancel₀]
  exact (Valuation.ne_zero_iff _).mpr hden

theorem exists_pow_valuation_eq [CharZero K] [Algebra ℚ K] (hqA : (q : K) ∈ A.nonunits) {x : K}
    (hx : IsAlgebraic ℚ x) (hx0 : x ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ ∃ a b : ℕ, w x ^ k * w (q : K) ^ a = w (q : K) ^ b := by
  obtain ⟨p, hp0, hpx⟩ := hx

  set t : ℕ → K := fun i => (p.coeff i : K) * x ^ i with ht
  have hsum : ∑ i ∈ Finset.range (p.natDegree + 1), t i = 0 := by
    rw [← hpx, aeval_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ht, Algebra.smul_def, eq_ratCast]
  have hlead : t p.natDegree ≠ 0 := by
    rw [ht]
    exact mul_ne_zero (by exact_mod_cast (leadingCoeff_ne_zero.mpr hp0)) (pow_ne_zero _ hx0)
  obtain ⟨i, hi, j, hj, hij, hti, htj, hv⟩ := exists_ne_val_eq_of_sum_eq_zero (w)
    (Finset.range (p.natDegree + 1)) t hsum (Finset.self_mem_range_succ _) hlead

  have hci : p.coeff i ≠ 0 := by
    intro h; apply hti; rw [ht]; simp only [h, Rat.cast_zero, zero_mul]
  have hcj : p.coeff j ≠ 0 := by
    intro h; apply htj; rw [ht]; simp only [h, Rat.cast_zero, zero_mul]

  wlog hlt : i < j generalizing i j
  · exact this j hj i hi hij.symm htj hti hv.symm hcj hci (lt_of_le_of_ne (not_lt.mp hlt) hij.symm)
  obtain ⟨ai, bi, hei⟩ := exists_valuation_ratCast_eq A hqA hci
  obtain ⟨aj, bj, hej⟩ := exists_valuation_ratCast_eq A hqA hcj
  refine ⟨j - i, Nat.sub_pos_of_lt hlt, bj + ai, bi + aj, ?_⟩

  have hx' : w x ^ i ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr hx0)
  have hkey : w x ^ (j - i) * w (p.coeff j : K) = w (p.coeff i : K) := by
    have h := hv
    rw [ht] at h
    simp only [map_mul, map_pow] at h

    rw [← pow_sub_mul_pow (w x) hlt.le] at h
    have h' : w (p.coeff i : K) * w x ^ i = (w x ^ (j - i) * w (p.coeff j : K)) * w x ^ i := by
      rw [h]; ac_rfl
    exact (mul_right_cancel₀ hx' h').symm
  rw [pow_add, pow_add, ← hej, ← hei, ← hkey]
  ac_rfl

theorem exists_pow_eq_mul_of_mem_maximalIdeal [CharZero K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (hqA : (q : K) ∈ A.nonunits) (c : A) (hc0 : c ≠ 0) (c' : A)
    (hc' : c' ∈ IsLocalRing.maximalIdeal A) (hc'0 : c' ≠ 0) :
    ∃ M : ℕ, ∃ a : A, (c' : K) ^ M = c * a := by
  have hcK : (c : K) ≠ 0 := fun h => hc0 (Subtype.ext h)
  have hc'K : (c' : K) ≠ 0 := fun h => hc'0 (Subtype.ext h)
  have hq1 : w (q : K) ≤ 1 := le_of_lt ((A.mem_nonunits_iff).mp hqA)
  obtain ⟨k, hk, a, b, he⟩ := exists_pow_valuation_eq A hqA (Algebra.IsAlgebraic.isAlgebraic _) hcK
  obtain ⟨k', hk', a', b', he'⟩ := exists_pow_valuation_eq A hqA (Algebra.IsAlgebraic.isAlgebraic _) hc'K
  have hvc : w (c : K) ≤ 1 := A.valuation_le_one c
  have hvc' : w (c' : K) < 1 := (A.valuation_lt_one_iff c').mp hc'
  have hqpos : ∀ n : ℕ, 0 < w (q : K) ^ n := fun n =>
    pow_pos ((Valuation.pos_iff _).mpr (by exact_mod_cast hq.out.ne_zero)) n

  have hcb : w (q : K) ^ b ≤ w (c : K) := by
    calc w (q : K) ^ b = w (c : K) ^ k * w (q : K) ^ a := he.symm
      _ ≤ w (c : K) ^ k * 1 := mul_le_mul_right (pow_le_one' hq1 a) _
      _ = w (c : K) ^ k := mul_one _
      _ ≤ w (c : K) := pow_le_of_le_one zero_le' hvc hk.ne'

  have hlt' : a' < b' := by
    by_contra hge
    push_neg at hge
    have h1 : w (c' : K) ^ k' < 1 := pow_lt_one' hvc' hk'.ne'
    have : w (q : K) ^ b' < w (q : K) ^ a' := by
      calc w (q : K) ^ b' = w (c' : K) ^ k' * w (q : K) ^ a' := he'.symm
        _ < 1 * w (q : K) ^ a' := mul_lt_mul_of_pos_right h1 (hqpos a')
        _ = w (q : K) ^ a' := one_mul _
    exact absurd (pow_le_pow_right_of_le_one' hq1 hge) (not_le.mpr this)
  have hc'q : w (c' : K) ^ k' ≤ w (q : K) := by
    have h : w (c' : K) ^ k' * w (q : K) ^ a' = (w (q : K) ^ (b' - a' - 1) * w (q : K)) * w (q : K) ^ a' := by
      rw [he', ← pow_succ, ← pow_add]; congr 1; omega
    have h2 := mul_right_cancel₀ (hqpos a').ne' h
    rw [h2]
    calc w (q : K) ^ (b' - a' - 1) * w (q : K) ≤ 1 * w (q : K) :=
          mul_le_mul_left (pow_le_one' hq1 _) _
      _ = w (q : K) := one_mul _

  refine ⟨k' * b, ⟨(c' : K) ^ (k' * b) * (c : K)⁻¹, ?_⟩, ?_⟩
  · rw [← A.valuation_le_one_iff, map_mul, map_inv₀, map_pow, pow_mul]
    calc (w (c' : K) ^ k') ^ b * (w (c : K))⁻¹ ≤ w (q : K) ^ b * (w (c : K))⁻¹ :=
          mul_le_mul_left (pow_le_pow_left' hc'q b) _
      _ ≤ w (c : K) * (w (c : K))⁻¹ := mul_le_mul_left hcb _
      _ = 1 := mul_inv_cancel₀ ((Valuation.ne_zero_iff _).mpr hcK)
  · show (c' : K) ^ (k' * b) = c * ((c' : K) ^ (k' * b) * (c : K)⁻¹)
    rw [mul_comm (c : K), mul_assoc, inv_mul_cancel₀ hcK, mul_one]

theorem map_eq_zero_of_mem_maximalIdeal [CharZero K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (hqA : (q : K) ∈ A.nonunits) {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) : red a = 0 := by
  by_cases ha0 : a = 0
  · rw [ha0, map_zero]
  have hqmem : (q : K) ∈ A := natCast_mem A q
  have hq0 : (⟨(q : K), hqmem⟩ : A) ≠ 0 := by
    intro h
    have := congrArg (fun z : A => (z : K)) h
    simp only [ZeroMemClass.coe_zero, Nat.cast_eq_zero] at this
    exact hq.out.ne_zero this
  obtain ⟨M, b, hMb⟩ := exists_pow_eq_mul_of_mem_maximalIdeal A hqA ⟨(q : K), hqmem⟩ hq0 a ha ha0
  have hA : a ^ M = ⟨(q : K), hqmem⟩ * b := Subtype.ext (by simpa using hMb)
  have hred : red a ^ M = 0 := by
    rw [← map_pow, hA, map_mul, show red ⟨(q : K), hqmem⟩ = (q : k) from ?_, CharP.cast_eq_zero,
      zero_mul]
    rw [← map_natCast red q]
    congr 1
  by_cases hM : M = 0
  · rw [hM, pow_zero] at hred; exact absurd hred one_ne_zero
  · exact pow_eq_zero_iff hM |>.mp hred

theorem exists_pow_eq_mul_of_mem_maximalIdeal_algebraicClosure
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hqA : (q : AlgebraicClosure ℚ) ∈ A.nonunits)
    (c : A) (hc0 : c ≠ 0) (c' : A) (hc' : c' ∈ IsLocalRing.maximalIdeal A) (hc'0 : c' ≠ 0) :
    ∃ M : ℕ, ∃ a : A, (c' : AlgebraicClosure ℚ) ^ M = c * a :=
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  exists_pow_eq_mul_of_mem_maximalIdeal A hqA c hc0 c' hc' hc'0

theorem map_eq_zero_of_mem_maximalIdeal_algebraicClosure
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hqA : (q : AlgebraicClosure ℚ) ∈ A.nonunits)
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) : red a = 0 :=
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  map_eq_zero_of_mem_maximalIdeal A hqA red a ha

end Archimedean

end Ws25.Archimedean

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} [Fact q.Prime]
    (hq : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    (c : A) (hc : c ≠ 0) (c' : A) (hc' : c' ∈ IsLocalRing.maximalIdeal A) (hc'0 : c' ≠ 0) :
    ∃ M : ℕ, c ∣ c' ^ M := by
  obtain ⟨M, a, h⟩ :=
    Ws25.Archimedean.exists_pow_eq_mul_of_mem_maximalIdeal_algebraicClosure A hq c hc c' hc' hc'0
  exact ⟨M, a, Subtype.ext (by simpa using h)⟩

end S_ValuationSubring_exists_dvd_pow_of_mem_maximalIdeal
end P2MW
export P2MW.S_ValuationSubring_exists_dvd_pow_of_mem_maximalIdeal (solution)
