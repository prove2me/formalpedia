-- Prove2me | solution 1 for OddPerfectNumber.dvd_succ_of_sigma_dvd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T09:01:31.327009+00:00
-- url     : https://prove2.me/submissions/34cf0eae-f83f-40b3-a0ff-6f6cbfacb84c

import Mathlib

open Finset

-- Solution to OddPerfectNumber.dvd_succ_of_sigma_dvd.
-- The DHP toolkit below (geometric sums, LTE, order extraction) is adapted
-- nearly verbatim from the local toolkit of the accepted Prove2Me proof of
-- OddPerfectNumber.no_dris_five_s_odd_eq_three (Gabewhigham), where every line
-- already verified remotely. Only the final solution wrapper is new.

namespace DHP

/-- `σ(p^k)` as a geometric sum. -/
lemma sigma_prime_pow (p k : ℕ) (hp : p.Prime) :
    ∑ d ∈ (p ^ k).divisors, d = ∑ i ∈ range (k + 1), p ^ i := by
  rw [Nat.sum_divisors_prime_pow hp]

/-- `(∑_{i<n} p^i) * (p-1) = p^n - 1`. -/
lemma geom_mul_sub_one (p n : ℕ) (hp : 1 ≤ p) :
    (∑ i ∈ range n, p ^ i) * (p - 1) = p ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    have h1 : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp
    have h2 : p ^ n ≤ p ^ (n + 1) := Nat.pow_le_pow_right hp (by omega)
    have : p ^ n * (p - 1) = p ^ (n + 1) - p ^ n := by
      rw [Nat.mul_sub, mul_one, pow_succ]
    omega

/-- Peeling off the constant term of a geometric sum. -/
lemma geom_succ (q n : ℕ) : ∑ i ∈ range (n + 1), q ^ i = q * (∑ i ∈ range n, q ^ i) + 1 := by
  rw [Finset.sum_range_succ']
  simp [Finset.mul_sum, pow_succ, mul_comm]

/-- Lifting the exponent, specialised to `x^n - 1` for an odd prime `q` with `q ∣ x - 1`. -/
lemma lte_sub_one {q x n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hx : 1 < x) (hqx : q ∣ x - 1)
    (hn : n ≠ 0) :
    padicValNat q (x ^ n - 1) = padicValNat q (x - 1) + padicValNat q n := by
  have : Fact q.Prime := ⟨hq⟩
  have hodd : Odd q := hq.odd_of_ne_two hq2
  have hnx : ¬ q ∣ x := by
    intro hdvd
    have h1 : q ∣ x - (x - 1) := Nat.dvd_sub hdvd hqx
    have hx1 : x - (x - 1) = 1 := by omega
    rw [hx1] at h1
    exact hq.one_lt.ne' (Nat.dvd_one.mp h1)
  have := padicValNat.pow_sub_pow (p := q) hodd (y := 1) hx (by simpa using hqx) hnx hn
  simpa using this

/-- If `σ(q^{2a}) = p^y` then `p^y - 1` has `q`-adic valuation exactly one. -/
lemma val_p_pow_sub_one {q y p : ℕ} (hq : q.Prime) (a : ℕ) (ha : a ≠ 0)
    (h : ∑ i ∈ range (2 * a + 1), q ^ i = p ^ y) :
    padicValNat q (p ^ y - 1) = 1 := by
  have : Fact q.Prime := ⟨hq⟩
  set S := ∑ i ∈ range (2 * a), q ^ i with hS
  have h1 : p ^ y = q * S + 1 := by rw [← h, geom_succ]
  have h2 : p ^ y - 1 = q * S := by omega
  obtain ⟨b, hb⟩ : ∃ b, 2 * a = b + 1 := ⟨2 * a - 1, by omega⟩
  have hSne : ¬ q ∣ S := by
    rw [hS, hb, geom_succ]
    intro hd
    have : q ∣ 1 := (Nat.dvd_add_right (Dvd.intro _ rfl)).mp hd
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  have hSpos : S ≠ 0 := by rw [hS, hb, geom_succ]; omega
  rw [h2, padicValNat.mul hq.ne_zero hSpos, padicValNat.self hq.one_lt,
    padicValNat.eq_zero_of_not_dvd hSne]

/-- Splitting off the `q`-part of `m`. -/
lemma split_prime_part {q m : ℕ} (hq : q.Prime) (hm : m ≠ 0) (hqm : q ∣ m) :
    ∃ a w, 1 ≤ a ∧ m = q ^ a * w ∧ ¬ q ∣ w :=
  ⟨m.factorization q, m / q ^ (m.factorization q),
    hq.factorization_pos_of_dvd hm hqm, (Nat.ordProj_mul_ordCompl_eq_self m q).symm,
    Nat.not_dvd_ordCompl hq hm⟩

/-- Congruence `p^n ≡ 1 (mod q)` in `ZMod q` versus divisibility in `ℕ`. -/
lemma zmod_pow_eq_one_iff {q p n : ℕ} (hp : 1 ≤ p) :
    ((p : ZMod q) ^ n = 1) ↔ q ∣ p ^ n - 1 := by
  have hpn : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp
  rw [← Nat.modEq_iff_dvd' hpn]
  constructor
  · intro h
    have : ((p ^ n : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by push_cast; simpa using h
    exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp this).symm
  · intro h
    have : ((p ^ n : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr h.symm
    push_cast at this
    simpa using this

/-- **Step A, general form.** If `q^2` divides the geometric sum `σ(p^k)` and the divisor sum
`σ(q^(2a))` of a nontrivial even power of `q` divides `p^k`, then `q ∣ k + 1`. -/
lemma dvd_succ_of_sigma_dvd {p k q a : ℕ} (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : a ≠ 0)
    (hq2S : q ^ 2 ∣ ∑ i ∈ range (k + 1), p ^ i)
    (hdvd : (∑ i ∈ range (2 * a + 1), q ^ i) ∣ p ^ k) : q ∣ k + 1 := by
  have : Fact q.Prime := ⟨hq⟩
  have hp1 : 1 < p := hp.one_lt
  set S := ∑ i ∈ range (k + 1), p ^ i with hSdef
  have hSne : S ≠ 0 := by rw [hSdef, geom_succ]; omega
  have hgeom : S * (p - 1) = p ^ (k + 1) - 1 := geom_mul_sub_one p (k + 1) hp.pos
  have hpk1 : p ^ 1 ≤ p ^ (k + 1) := Nat.pow_le_pow_right hp.pos (by omega)
  have hne : p ^ (k + 1) - 1 ≠ 0 := by simp only [pow_one] at hpk1; omega
  have hvalS : 2 ≤ padicValNat q S := (padicValNat_dvd_iff_le hSne).mp hq2S
  have hsplit : padicValNat q (p ^ (k + 1) - 1) = padicValNat q S + padicValNat q (p - 1) := by
    rw [← hgeom, padicValNat.mul hSne (by omega)]
  obtain ⟨y, _, hy⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, pow_zero, geom_succ] at hy
    have hT : (∑ i ∈ range (2 * a), q ^ i) ≠ 0 := by
      obtain ⟨b, hb⟩ : ∃ b, 2 * a = b + 1 := ⟨2 * a - 1, by omega⟩
      rw [hb, geom_succ]; omega
    have hzero : q * (∑ i ∈ range (2 * a), q ^ i) = 0 := by omega
    rcases Nat.mul_eq_zero.mp hzero with h | h
    · exact hq.ne_zero h
    · exact hT h
  have hvalpy : padicValNat q (p ^ y - 1) = 1 := val_p_pow_sub_one hq a ha hy
  have hpy1 : p ^ 1 ≤ p ^ y := Nat.pow_le_pow_right hp.pos (by omega)
  have hpyne : p ^ y - 1 ≠ 0 := by simp only [pow_one] at hpy1; omega
  by_cases hqp1 : q ∣ p - 1
  · have hlte := lte_sub_one hq hq2 hp1 hqp1 (n := k + 1) (by omega)
    rw [hsplit] at hlte
    have h1' : 1 ≤ padicValNat q (k + 1) := by omega
    simpa using (padicValNat_dvd_iff_le (p := q) (a := k + 1) (n := 1) (by omega)).mpr h1'
  · have hvalp1 : padicValNat q (p - 1) = 0 := padicValNat.eq_zero_of_not_dvd hqp1
    have hqS : q ∣ S := dvd_trans (dvd_pow_self q two_ne_zero) hq2S
    have hqpk : q ∣ p ^ (k + 1) - 1 := by rw [← hgeom]; exact hqS.mul_right _
    have hek : orderOf (p : ZMod q) ∣ k + 1 :=
      orderOf_dvd_of_pow_eq_one ((zmod_pow_eq_one_iff hp.pos).mpr hqpk)
    have he0 : orderOf (p : ZMod q) ≠ 0 := by
      intro h0
      rw [h0] at hek
      exact absurd (Nat.eq_zero_of_zero_dvd hek) (by omega)
    set e := orderOf (p : ZMod q) with he
    have hqpe : q ∣ p ^ e - 1 := (zmod_pow_eq_one_iff hp.pos).mp (pow_orderOf_eq_one _)
    have hpe1 : 1 < p ^ e := by
      calc 1 < p := hp1
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos (by omega)
    have hpene : p ^ e - 1 ≠ 0 := by omega
    have hey : e ∣ y := by
      refine orderOf_dvd_of_pow_eq_one ((zmod_pow_eq_one_iff hp.pos).mpr ?_)
      simpa using (padicValNat_dvd_iff_le (p := q) (a := p ^ y - 1) (n := 1) hpyne).mpr (by omega)
    have hveq : padicValNat q (p ^ e - 1) = 1 := by
      have hdvd_e_y : p ^ e - 1 ∣ p ^ y - 1 := by
        obtain ⟨c, rfl⟩ := hey
        simpa [← pow_mul] using Nat.sub_dvd_pow_sub_pow (p ^ e) 1 c
      have hlow : 1 ≤ padicValNat q (p ^ e - 1) :=
        (padicValNat_dvd_iff_le (p := q) (a := p ^ e - 1) (n := 1) hpene).mp (by simpa using hqpe)
      by_contra hcon
      have h2' : 2 ≤ padicValNat q (p ^ e - 1) := by omega
      have : q ^ 2 ∣ p ^ y - 1 :=
        dvd_trans ((padicValNat_dvd_iff_le (p := q) hpene).mpr h2') hdvd_e_y
      have := (padicValNat_dvd_iff_le (p := q) (a := p ^ y - 1) (n := 2) hpyne).mp this
      omega
    obtain ⟨c, hc⟩ := hek
    have hc0 : c ≠ 0 := by rintro rfl; omega
    have hlte := lte_sub_one hq hq2 hpe1 hqpe hc0
    rw [← pow_mul, ← hc, hsplit, hvalp1, hveq] at hlte
    have h1' : 1 ≤ padicValNat q c := by omega
    have hqc : q ∣ c := by
      simpa using (padicValNat_dvd_iff_le (p := q) (a := c) (n := 1) hc0).mpr h1'
    exact hc ▸ hqc.mul_left e
end DHP

theorem solution (p k q a : Nat) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (ha : a ≠ 0)
    (hq2S : q ^ 2 ∣ ∑ i ∈ Finset.range (k + 1), p ^ i)
    (hdvd : (∑ i ∈ Finset.range (2 * a + 1), q ^ i) ∣ p ^ k) : q ∣ k + 1 :=
  DHP.dvd_succ_of_sigma_dvd hp hq hq2 ha hq2S hdvd
