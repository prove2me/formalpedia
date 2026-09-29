-- Prove2me | solution 1 for OddPerfectNumber.dandapat_hunsucker_pomerance_two
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-11T06:40:13.347324+00:00
-- url     : https://prove2.me/submissions/7251a185-090e-4233-9da1-f6c1985d7a3d

import Mathlib

/-!
Proof of `OddPerfectNumber.dandapat_hunsucker_pomerance_two`: the system
`σ(p^k) = 2m²`, `σ(m²) = p^k` has no solution with `p` prime, `m` odd and `k ≠ 0`.
-/

open Finset

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

/-- Geometric sums mod `r`, when `p ≡ 1 [MOD r]`. -/
lemma geom_mod (p n r : ℕ) (h : p % r = 1 % r) :
    (∑ i ∈ range n, p ^ i) % r = n % r := by
  rw [Finset.sum_nat_mod]
  have : ∀ i ∈ range n, p ^ i % r = 1 % r := by
    intro i _
    rw [Nat.pow_mod, h, ← Nat.pow_mod, one_pow]
  rw [Finset.sum_congr rfl this]
  simp [Finset.sum_const]

/-- Divisibility of geometric sums. -/
lemma geom_dvd_geom {p d n : ℕ} (hp : 2 ≤ p) (h : d ∣ n) :
    (∑ i ∈ range d, p ^ i) ∣ (∑ i ∈ range n, p ^ i) := by
  obtain ⟨c, rfl⟩ := h
  have key : (p ^ d - 1) ∣ (p ^ (d * c) - 1) := by
    have := Nat.sub_dvd_pow_sub_pow (p ^ d) 1 c
    simpa [← pow_mul] using this
  rw [← geom_mul_sub_one p d (by omega), ← geom_mul_sub_one p (d * c) (by omega)] at key
  exact (Nat.mul_dvd_mul_iff_right (by omega : 0 < p - 1)).mp key

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

/-- **Step A.** Every prime `q` dividing `m` divides `k + 1`. -/
lemma prime_dvd_succ {p k m q : ℕ} (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqm : q ∣ m) (hm0 : m ≠ 0)
    (h1 : ∑ i ∈ range (k + 1), p ^ i = 2 * m ^ 2)
    (h2 : ∑ d ∈ (m ^ 2).divisors, d = p ^ k) : q ∣ k + 1 := by
  have : Fact q.Prime := ⟨hq⟩
  have hp1 : 1 < p := hp.one_lt
  set S := ∑ i ∈ range (k + 1), p ^ i with hSdef
  have hSne : S ≠ 0 := by rw [hSdef, geom_succ]; omega
  have hq2S : q ^ 2 ∣ S := h1 ▸ Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hqm 2) 2
  have hgeom : S * (p - 1) = p ^ (k + 1) - 1 := geom_mul_sub_one p (k + 1) hp.pos
  have hpk1 : p ^ 1 ≤ p ^ (k + 1) := Nat.pow_le_pow_right hp.pos (by omega)
  have hne : p ^ (k + 1) - 1 ≠ 0 := by simp only [pow_one] at hpk1; omega
  have hvalS : 2 ≤ padicValNat q S := (padicValNat_dvd_iff_le hSne).mp hq2S
  have hsplit : padicValNat q (p ^ (k + 1) - 1) = padicValNat q S + padicValNat q (p - 1) := by
    rw [← hgeom, padicValNat.mul hSne (by omega)]
  -- the `q`-part of `m` gives `σ(q^(2a)) = p^y`
  obtain ⟨a, w, ha, hmw, hqw⟩ := split_prime_part hq hm0 hqm
  have hm2 : m ^ 2 = q ^ (2 * a) * w ^ 2 := by rw [hmw]; ring
  have hcop : Nat.Coprime (q ^ (2 * a)) (w ^ 2) :=
    Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqw)
  have hdvd : (∑ i ∈ range (2 * a + 1), q ^ i) ∣ p ^ k := by
    rw [← sigma_prime_pow q (2 * a) hq, ← h2, hm2, hcop.sum_divisors_mul]
    exact Dvd.intro _ rfl
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
  have hvalpy : padicValNat q (p ^ y - 1) = 1 := val_p_pow_sub_one hq a (by omega) hy
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

/-- **Main theorem.** The system `σ(p^k) = 2m²`, `σ(m²) = p^k` has no solution with `p` prime,
`m` odd and `k ≠ 0`. -/
theorem no_solution {p k m : ℕ} (hp : p.Prime) (hm : Odd m) (hk : k ≠ 0)
    (h1 : ∑ d ∈ (p ^ k).divisors, d = 2 * m ^ 2)
    (h2 : ∑ d ∈ (m ^ 2).divisors, d = p ^ k) : False := by
  rw [sigma_prime_pow p k hp] at h1
  have hp1 : 1 < p := hp.one_lt
  -- `p` is odd
  have hp2 : p ≠ 2 := by
    intro h
    subst h
    rw [geom_succ] at h1
    omega
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  -- `m` is neither `0` nor `1`
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hm1 : m ≠ 1 := by
    rintro rfl
    simp at h2
    have : p ^ 1 ≤ p ^ k := Nat.pow_le_pow_right hp.pos (by omega)
    simp only [pow_one] at this
    omega
  -- the largest prime factor `q` of `m`
  have hne : m.primeFactors.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, Nat.primeFactors_eq_empty]
    intro h
    rcases h with h | h
    · exact hm0 h
    · exact hm1 h
  set q := m.primeFactors.max' hne with hqdef
  have hqmem : q ∈ m.primeFactors := m.primeFactors.max'_mem hne
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqmem
  have hqm : q ∣ m := Nat.dvd_of_mem_primeFactors hqmem
  have hqmax : ∀ r ∈ m.primeFactors, r ≤ q := fun r hr => m.primeFactors.le_max' r hr
  have hq2 : q ≠ 2 := by
    intro h
    rw [h] at hqm
    rw [Nat.odd_iff] at hm
    omega
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two hq2)
  -- Step A
  have hqk : q ∣ k + 1 := prime_dvd_succ hp hq hq2 hqm hm0 h1 h2
  -- Step B : the `q`-th geometric sum divides `2m²`
  set A := ∑ i ∈ range q, p ^ i with hAdef
  have hAdvd : A ∣ 2 * m ^ 2 := h1 ▸ geom_dvd_geom hp.two_le hqk
  have hAodd : A % 2 = 1 := by
    rw [hAdef, geom_mod p q 2 (by omega)]
    exact hqodd
  have hgeomA : A * (p - 1) = p ^ q - 1 := geom_mul_sub_one p q hp.pos
  -- Step C : every prime divisor of `A` equals `q`, and then `q ∣ p - 1`
  have key : ∀ r : ℕ, r.Prime → r ∣ A → r = q ∧ q ∣ p - 1 := by
    intro r hr hrA
    have hr2 : r ≠ 2 := by
      rintro rfl
      omega
    have hrm : r ∣ m := by
      rcases (Nat.Prime.dvd_mul hr).mp (hrA.trans hAdvd) with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h) hr2
      · exact hr.dvd_of_dvd_pow h
    have hrq : r ≤ q := hqmax r (Nat.mem_primeFactors.mpr ⟨hr, hrm, hm0⟩)
    have hrpq : r ∣ p ^ q - 1 := hgeomA ▸ hrA.mul_right _
    by_cases hrp : r ∣ p - 1
    · have hmod : A % r = q % r := by
        rw [hAdef]
        exact geom_mod p q r (((Nat.modEq_iff_dvd' hp.one_le).mpr hrp).symm)
      have hA0 : A % r = 0 := Nat.dvd_iff_mod_eq_zero.mp hrA
      have hrq' : r ∣ q := Nat.dvd_of_mod_eq_zero (by omega)
      have hreq : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp hrq'
      exact ⟨hreq, hreq ▸ hrp⟩
    · have : Fact r.Prime := ⟨hr⟩
      have hq0 : q ≠ 0 := hq.ne_zero
      have hrnp : ¬ r ∣ p := by
        intro hd
        have h1' : r ∣ p ^ q := dvd_pow hd hq0
        have hpq1 : 1 ≤ p ^ q := Nat.one_le_pow _ _ hp.pos
        have hd1 : r ∣ p ^ q - (p ^ q - 1) := Nat.dvd_sub h1' hrpq
        rw [show p ^ q - (p ^ q - 1) = 1 by omega] at hd1
        exact hr.one_lt.ne' (Nat.dvd_one.mp hd1)
      have hp0 : (p : ZMod r) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact hrnp
      have hord : orderOf (p : ZMod r) ∣ q :=
        orderOf_dvd_of_pow_eq_one ((zmod_pow_eq_one_iff hp.pos).mpr hrpq)
      have hne1 : orderOf (p : ZMod r) ≠ 1 := by
        intro h
        have hone : (p : ZMod r) = 1 := orderOf_eq_one_iff.mp h
        have hone' : ((p : ZMod r)) ^ 1 = 1 := by simpa using hone
        have := (zmod_pow_eq_one_iff (q := r) (p := p) (n := 1) hp.pos).mp hone'
        simp only [pow_one] at this
        exact hrp this
      have hordq : orderOf (p : ZMod r) = q :=
        ((hq.eq_one_or_self_of_dvd _ hord).resolve_left hne1)
      have hqr : q ∣ r - 1 := hordq ▸ ZMod.orderOf_dvd_card_sub_one hp0
      have : q ≤ r - 1 := Nat.le_of_dvd (by have := hr.two_le; omega) hqr
      have := hr.two_le
      omega
  -- Step D : `q ∣ A` and `q ∣ p - 1`
  have hA1 : q < A := by
    have hpow : ∀ i ∈ range q, 2 ^ i ≤ p ^ i := fun i _ => Nat.pow_le_pow_left hp.two_le i
    have hsum : ∑ i ∈ range q, 2 ^ i ≤ A := Finset.sum_le_sum hpow
    have h2q : ∑ i ∈ range q, 2 ^ i = 2 ^ q - 1 := by
      have := geom_mul_sub_one 2 q (by omega)
      simpa using this
    have hq3 : 3 ≤ q := by
      have := hq.two_le
      omega
    have hlt : q - 1 < 2 ^ (q - 1) := Nat.lt_two_pow_self
    have : 2 ^ q = 2 * 2 ^ (q - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  have hAminfac : (A.minFac).Prime := Nat.minFac_prime (by omega)
  obtain ⟨hqeq, hqp1⟩ := key A.minFac hAminfac (Nat.minFac_dvd A)
  have hqA : q ∣ A := hqeq ▸ Nat.minFac_dvd A
  -- the `q`-adic valuation of `A` is one
  have : Fact q.Prime := ⟨hq⟩
  have hApos : A ≠ 0 := by omega
  have hlte := lte_sub_one hq hq2 hp1 hqp1 (n := q) hq.ne_zero
  rw [← hgeomA, padicValNat.mul hApos (by omega), padicValNat.self hq.one_lt] at hlte
  have hvalA : padicValNat q A = 1 := by omega
  -- but `q² ∣ A`, a contradiction
  have hB1 : 1 < A / q := by
    have := Nat.div_mul_cancel hqA
    have hq2' := hq.two_le
    rcases Nat.lt_or_ge (A / q) 2 with h | h
    · interval_cases hh : (A / q) <;> omega
    · omega
  have hBminfac : ((A / q).minFac).Prime := Nat.minFac_prime (by omega)
  have hBdvd : (A / q).minFac ∣ A :=
    dvd_trans (Nat.minFac_dvd _) (Nat.div_dvd_of_dvd hqA)
  have hBq : (A / q).minFac = q := (key _ hBminfac hBdvd).1
  have hqB : q ∣ A / q := by
    have h := Nat.minFac_dvd (A / q)
    rwa [hBq] at h
  have hq2A : q ^ 2 ∣ A := by
    obtain ⟨t, ht⟩ := hqB
    refine ⟨t, ?_⟩
    have := Nat.div_mul_cancel hqA
    rw [ht] at this
    rw [← this]
    ring
  have := (padicValNat_dvd_iff_le (p := q) (a := A) (n := 2) hApos).mp hq2A
  omega

end DHP

theorem solution (p k m : ℕ) (hp : p.Prime) (hm : Odd m) (hk : k ≠ 0)
    (h1 : (∑ d ∈ (p ^ k).divisors, d) = 2 * m ^ 2)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ k) : False :=
  DHP.no_solution hp hm hk h1 h2
