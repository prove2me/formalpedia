-- Prove2me | solution 1 for ValuationSubring.ringHom_apply_eq_zero_of_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/4e4d96a7-6ba0-5052-ab0c-ae264c807479

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_ringHom_apply_eq_zero_of_mem_maximalIdeal
set_option autoImplicit false

open IsLocalRing Polynomial

namespace ValuationSubring
p2m_export "ValuationSubring" "valuation_eq_iff ext valuation_le_one valuation_lt_one_iff valuation"
p2m_open "ValuationSubring"

variable {K : Type*} [Field K]

private theorem _root_.ValuationSubring.valuation_intCast_le_one (A : ValuationSubring K) (a : ℤ) : A.valuation (a : K) ≤ 1 := by
  have h := A.valuation_le_one (a : A)
  simpa using h

p2m_export "ValuationSubring" "valuation_intCast_le_one"

private theorem _root_.ValuationSubring.valuation_natCast_eq_one_of_not_dvd (A : ValuationSubring K) {p : ℕ} (hp : p.Prime)
    (hvp : A.valuation (p : K) < 1) {n : ℕ} (hn : ¬ p ∣ n) : A.valuation (n : K) = 1 := by
  have hcop : IsCoprime (p : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn)
  obtain ⟨a, b, hab⟩ := hcop
  have habK : (a : K) * (p : K) + (b : K) * (n : K) = 1 := by exact_mod_cast congrArg (fun z : ℤ => (z : K)) hab
  apply le_antisymm
  · simpa using A.valuation_intCast_le_one n
  · by_contra hlt
    push Not at hlt
    have h1 : A.valuation ((a : K) * (p : K)) < 1 := by
      rw [map_mul]
      calc A.valuation (a : K) * A.valuation (p : K) ≤ 1 * A.valuation (p : K) :=
            mul_le_mul_left (A.valuation_intCast_le_one a) _
        _ < 1 := by rw [one_mul]; exact hvp
    have h2 : A.valuation ((b : K) * (n : K)) < 1 := by
      rw [map_mul]
      calc A.valuation (b : K) * A.valuation (n : K) ≤ 1 * A.valuation (n : K) :=
            mul_le_mul_left (A.valuation_intCast_le_one b) _
        _ < 1 := by rw [one_mul]; exact hlt
    have := A.valuation.map_add_lt h1 h2
    rw [habK, map_one] at this
    exact lt_irrefl _ this

p2m_export "ValuationSubring" "valuation_natCast_eq_one_of_not_dvd"
private theorem _root_.ValuationSubring.valuation_natCast_ne_zero (A : ValuationSubring K) [CharZero K] {n : ℕ} (hn : n ≠ 0) :
    A.valuation (n : K) ≠ 0 := by
  rw [ne_eq, Valuation.zero_iff]; exact_mod_cast hn

p2m_export "ValuationSubring" "valuation_natCast_ne_zero"

private theorem _root_.ValuationSubring.exists_valuation_ratCast_mul_pow_eq (A : ValuationSubring K) [CharZero K] {p : ℕ} (hp : p.Prime)
    (hvp : A.valuation (p : K) < 1) (c : ℚ) (hc : c ≠ 0) :
    ∃ s t : ℕ, A.valuation (c : K) * A.valuation (p : K) ^ t = A.valuation (p : K) ^ s := by
  have hnum : c.num ≠ 0 := Rat.num_ne_zero.mpr hc
  have hden : c.den ≠ 0 := c.den_nz
  obtain ⟨s, n', hn', hns⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hnum) p hp.ne_one
  obtain ⟨t, d', hd', hdt⟩ := Nat.exists_eq_pow_mul_and_not_dvd hden p hp.ne_one
  refine ⟨s, t, ?_⟩
  have hvn' := A.valuation_natCast_eq_one_of_not_dvd hp hvp hn'
  have hvd' := A.valuation_natCast_eq_one_of_not_dvd hp hvp hd'
  have hvnum : A.valuation (c.num : K) = A.valuation (p : K) ^ s := by
    have habs : A.valuation (c.num : K) = A.valuation ((c.num.natAbs : ℕ) : K) := by
      rcases Int.natAbs_eq c.num with h | h
      · conv_lhs => rw [h]
        simp
      · conv_lhs => rw [h]
        simp [Valuation.map_neg]
    rw [habs, hns]; push_cast; rw [map_mul, map_pow, hvn', mul_one]
  have hvden : A.valuation (c.den : K) = A.valuation (p : K) ^ t := by
    rw [hdt]; push_cast; rw [map_mul, map_pow, hvd', mul_one]
  have hcK : (c : K) = (c.num : K) / (c.den : K) := by rw [Rat.cast_def]
  have hpt : A.valuation (p : K) ^ t ≠ 0 := pow_ne_zero _ (A.valuation_natCast_ne_zero hp.ne_zero)
  rw [hcK, map_div₀, hvnum, hvden, div_mul_cancel₀ _ hpt]

p2m_export "ValuationSubring" "exists_valuation_ratCast_mul_pow_eq"

private theorem _root_.ValuationSubring.exists_pow_eq_of_two_terms (A : ValuationSubring K) [CharZero K] {p : ℕ} (hp : p.Prime)
    (hvp : A.valuation (p : K) < 1) {x : K} (hx0 : x ≠ 0) (hvx : A.valuation x < 1)
    {a b : ℕ} (hab : a < b) {ca cb : ℚ} (hca : ca ≠ 0) (hcb : cb ≠ 0)
    (heq : A.valuation ((ca : K) * x ^ a) = A.valuation ((cb : K) * x ^ b)) :
    ∃ m e : ℕ, 1 ≤ m ∧ 1 ≤ e ∧ A.valuation x ^ m = A.valuation (p : K) ^ e := by
  set v := A.valuation with hv
  have hvx0 : v x ≠ 0 := by rw [ne_eq, Valuation.zero_iff]; exact hx0
  have hvcb : v (cb : K) ≠ 0 := by rw [ne_eq, Valuation.zero_iff]; exact_mod_cast hcb

  have h1 : v (ca : K) = v (cb : K) * v x ^ (b - a) := by
    rw [map_mul, map_mul, map_pow, map_pow] at heq
    have hb : b = a + (b - a) := by omega
    rw [hb, pow_add, ← mul_assoc] at heq

    have hxa : v x ^ a ≠ 0 := pow_ne_zero _ hvx0
    have : v (ca : K) * v x ^ a = (v (cb : K) * v x ^ (b - a)) * v x ^ a := by rw [heq, mul_right_comm]
    exact mul_right_cancel₀ hxa this

  obtain ⟨s, t, hst⟩ := A.exists_valuation_ratCast_mul_pow_eq hp hvp (ca / cb) (div_ne_zero hca hcb)
  have hquot : v ((ca / cb : ℚ) : K) = v x ^ (b - a) := by
    push_cast
    rw [map_div₀, h1]
    exact mul_div_cancel_left₀ _ hvcb
  rw [hquot] at hst

  have hm : 1 ≤ b - a := by omega
  have hxlt : v x ^ (b - a) < 1 := pow_lt_one' hvx (by omega)
  have hpt0 : 0 < v (p : K) ^ t := pow_pos (zero_lt_iff.mpr (A.valuation_natCast_ne_zero hp.ne_zero)) _
  have hts : t < s := by
    by_contra hle
    push Not at hle
    have hpow : v (p : K) ^ t ≤ v (p : K) ^ s := pow_le_pow_right_of_le_one' hvp.le hle
    have : v x ^ (b - a) * v (p : K) ^ t < 1 * v (p : K) ^ t := mul_lt_mul_of_pos_right hxlt hpt0
    rw [one_mul, hst] at this
    exact absurd hpow (not_le.mpr this)
  refine ⟨b - a, s - t, hm, by omega, ?_⟩
  have hs : s = t + (s - t) := by omega
  rw [hs, pow_add] at hst
  have hpt : v (p : K) ^ t ≠ 0 := pow_ne_zero _ (A.valuation_natCast_ne_zero hp.ne_zero)
  have : v x ^ (b - a) * v (p : K) ^ t = v (p : K) ^ (s - t) * v (p : K) ^ t := by rw [hst, mul_comm]
  exact mul_right_cancel₀ hpt this

p2m_export "ValuationSubring" "exists_pow_eq_of_two_terms"

private theorem _root_.ValuationSubring.exists_valuation_pow_eq_pow (A : ValuationSubring K) [CharZero K] {p : ℕ} (hp : p.Prime)
    (hvp : A.valuation (p : K) < 1) {x : K} (hx0 : x ≠ 0) (hvx : A.valuation x < 1) (halg : IsAlgebraic ℚ x) :
    ∃ m e : ℕ, 1 ≤ m ∧ 1 ≤ e ∧ A.valuation x ^ m = A.valuation (p : K) ^ e := by
  classical
  set v := A.valuation with hv
  obtain ⟨P, hP0, hPx⟩ := halg
  set N := P.natDegree with hN
  let t : ℕ → K := fun i => (P.coeff i : K) * x ^ i
  have hsum : ∑ i ∈ Finset.range (N + 1), t i = 0 := by
    have := hPx
    rw [Polynomial.aeval_eq_sum_range] at this
    simpa [t, Algebra.smul_def, eq_ratCast] using this
  have htN : t N ≠ 0 := by
    simp only [t, ne_eq, mul_eq_zero, not_or]
    exact ⟨by exact_mod_cast (Polynomial.leadingCoeff_ne_zero.mpr hP0), pow_ne_zero _ hx0⟩
  obtain ⟨j, hjs, hjmax⟩ := Finset.exists_max_image (Finset.range (N + 1)) (fun i => v (t i))
    ⟨N, Finset.self_mem_range_succ N⟩
  have hvj0 : v (t j) ≠ 0 := by
    intro h0
    have := hjmax N (Finset.self_mem_range_succ N)
    rw [h0] at this
    exact htN ((Valuation.zero_iff v).mp (le_antisymm this zero_le'))
  obtain ⟨i, his, hij, hvi⟩ : ∃ i ∈ Finset.range (N + 1), i ≠ j ∧ v (t i) = v (t j) := by
    by_contra hnone
    push Not at hnone
    have hlt : ∀ i ∈ Finset.range (N + 1) \ {j}, v (t i) < v (t j) := by
      intro i hi
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
      exact lt_of_le_of_ne (hjmax i hi.1) (hnone i hi.1 hi.2)
    have := Valuation.map_sum_eq_of_lt v hjs hlt
    rw [hsum, map_zero] at this
    exact hvj0 this.symm
  have hvi0 : v (t i) ≠ 0 := hvi ▸ hvj0
  have hci : (P.coeff i : ℚ) ≠ 0 := by
    intro h0; apply hvi0; simp [t, h0]
  have hcj : (P.coeff j : ℚ) ≠ 0 := by
    intro h0; apply hvj0; simp [t, h0]
  rcases lt_or_gt_of_ne hij with h | h
  · exact A.exists_pow_eq_of_two_terms hp hvp hx0 hvx h hci hcj hvi
  · exact A.exists_pow_eq_of_two_terms hp hvp hx0 hvx h hcj hci hvi.symm

p2m_export "ValuationSubring" "exists_valuation_pow_eq_pow"

private theorem _root_.ValuationSubring.ringHom_apply_eq_zero_of_mem_maximalIdeal [CharZero K] [Algebra.IsAlgebraic ℚ K]
    (A : ValuationSubring K) {k : Type*} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    (f : A →+* k) {x : A} (hx : x ∈ maximalIdeal A) : f x = 0 := by
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]
  set v := A.valuation with hv
  have hPprime : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  have hpP : ((p : ℕ) : A) ∈ RingHom.ker f := by
    rw [RingHom.mem_ker, map_natCast]; exact CharP.cast_eq_zero k p
  have hPle : RingHom.ker f ≤ maximalIdeal A := le_maximalIdeal hPprime.ne_top
  have hvp : v ((p : ℕ) : K) < 1 := by
    have := (A.valuation_lt_one_iff ((p : ℕ) : A)).mp (hPle hpP)
    simpa using this
  have hvx : v (x : K) < 1 := (A.valuation_lt_one_iff x).mp hx
  have hxK : (x : K) ≠ 0 := by exact_mod_cast hx0
  have halg : IsAlgebraic ℚ (x : K) := Algebra.IsAlgebraic.isAlgebraic _
  obtain ⟨m, e, hm, he, hve⟩ := A.exists_valuation_pow_eq_pow hp.out hvp hxK hvx halg

  have hve' : v ((x : K) ^ m) = v (((p : ℕ) : K) ^ e) := by rw [map_pow, map_pow, hve]
  obtain ⟨u, hu⟩ := (A.valuation_eq_iff _ _).mp hve'

  have hxm : x ^ m = (u : A) * (p : A) ^ e := by
    apply Subtype.ext
    push_cast
    exact hu.symm
  have hmem : x ^ m ∈ RingHom.ker f := by
    rw [hxm]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hpP e he)
  exact (RingHom.mem_ker).mp (hPprime.mem_of_pow_mem m hmem)

p2m_export "ValuationSubring" "ringHom_apply_eq_zero_of_mem_maximalIdeal"
end ValuationSubring

theorem solution
    {K : Type*} [Field K] [CharZero K] [Algebra.IsAlgebraic ℚ K]
    (A : ValuationSubring K) {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : A →+* k) {x : A} (hx : x ∈ IsLocalRing.maximalIdeal A) : f x = 0 :=
  A.ringHom_apply_eq_zero_of_mem_maximalIdeal p f hx

end S_ValuationSubring_ringHom_apply_eq_zero_of_mem_maximalIdeal
end P2MW
export P2MW.S_ValuationSubring_ringHom_apply_eq_zero_of_mem_maximalIdeal (solution)
