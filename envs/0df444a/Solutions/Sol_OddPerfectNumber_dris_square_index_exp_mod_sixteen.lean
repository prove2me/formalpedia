-- Prove2me | solution 1 for OddPerfectNumber.dris_square_index_exp_mod_sixteen
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-11T13:29:00.484781+00:00
-- url     : https://prove2.me/submissions/bd4d130f-fed9-4212-91a0-f8e001fcc3c9

import Theorems.Thm_OddPerfectNumber_prime_and_exp_mod_sixteen_of_sigma_eq_two_mul_sq
import Theorems.Thm_OddPerfectNumber_sigma_prime_pow_ne_two_mul_sq_of_six_dvd

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

/-- **Step A.** Every prime `q` dividing `m` divides `k + 1`. -/
lemma prime_dvd_succ {p k m q : ℕ} (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqm : q ∣ m) (hm0 : m ≠ 0)
    (h1 : ∑ i ∈ range (k + 1), p ^ i = 2 * m ^ 2)
    (h2 : ∑ d ∈ (m ^ 2).divisors, d = p ^ k) : q ∣ k + 1 := by
  have hq2S : q ^ 2 ∣ ∑ i ∈ range (k + 1), p ^ i :=
    h1 ▸ Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hqm 2) 2
  obtain ⟨a, w, ha, hmw, hqw⟩ := split_prime_part hq hm0 hqm
  have hm2 : m ^ 2 = q ^ (2 * a) * w ^ 2 := by rw [hmw]; ring
  have hcop : Nat.Coprime (q ^ (2 * a)) (w ^ 2) :=
    Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqw)
  have hdvd : (∑ i ∈ range (2 * a + 1), q ^ i) ∣ p ^ k := by
    rw [← sigma_prime_pow q (2 * a) hq, ← h2, hm2, hcop.sum_divisors_mul]
    exact Dvd.intro _ rfl
  exact dvd_succ_of_sigma_dvd hp hq hq2 (by omega) hq2S hdvd

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


namespace DrisSupport

/-- `Ω` is monotone under divisibility. -/
lemma bigOmega_mono {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) :
    a.primeFactorsList.length ≤ b.primeFactorsList.length := by
  obtain ⟨c, rfl⟩ := h
  have ha : a ≠ 0 := by rintro rfl; simp at hb
  have hc : c ≠ 0 := by rintro rfl; simp at hb
  have := ArithmeticFunction.cardFactors_mul (m := a) (n := c) ha hc
  simp only [ArithmeticFunction.cardFactors_apply] at this
  omega

/-- A product of `E.card` factors each exceeding `1` has at least `E.card` prime factors,
counted with multiplicity. -/
lemma card_le_bigOmega_prod (f : ℕ → ℕ) :
    ∀ (E : Finset ℕ), (∀ q ∈ E, 1 < f q) →
      E.card ≤ (∏ q ∈ E, f q).primeFactorsList.length := by
  intro E
  induction E using Finset.induction_on with
  | empty => intro _; simp
  | insert a E ha ih =>
      intro hf
      have hfa : 1 < f a := hf a (Finset.mem_insert_self _ _)
      have hrest : ∀ q ∈ E, 1 < f q := fun q hq => hf q (Finset.mem_insert_of_mem hq)
      have hprod0 : (∏ q ∈ E, f q) ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr ?_
        intro q hq
        have := hrest q hq
        omega
      have hfa0 : f a ≠ 0 := by omega
      have hlen := ArithmeticFunction.cardFactors_mul (m := f a) (n := ∏ q ∈ E, f q) hfa0 hprod0
      simp only [ArithmeticFunction.cardFactors_apply] at hlen
      have hfa1 : 1 ≤ (f a).primeFactorsList.length := by
        have hpos : 0 < ArithmeticFunction.cardFactors (f a) :=
          ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hfa
        rw [ArithmeticFunction.cardFactors_apply] at hpos
        omega
      have := ih hrest
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, hlen]
      omega

/-- The divisor sum of a square, factored into its local divisor sums. -/
lemma sigma_sq_local_prod {m : ℕ} (hm : m ≠ 0) :
    (∑ x ∈ (m ^ 2).divisors, x) =
      ∏ q ∈ (m ^ 2).primeFactors, ∑ i ∈ range ((m ^ 2).factorization q + 1), q ^ i := by
  have hm2 : (m ^ 2) ≠ 0 := pow_ne_zero _ hm
  have h := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).multiplicative_factorization
    (ArithmeticFunction.sigma 1) hm2
  rw [ArithmeticFunction.sigma_one_apply] at h
  rw [h, Finsupp.prod]
  rw [Nat.support_factorization]
  refine Finset.prod_congr rfl ?_
  intro q hq
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  rw [ArithmeticFunction.sigma_one_apply, DHP.sigma_prime_pow q _ hqp]

/-- Each local divisor sum of `m²` exceeds `1`. -/
lemma one_lt_local {m q : ℕ} (hm : m ≠ 0) (hq : q ∈ (m ^ 2).primeFactors) :
    1 < ∑ i ∈ range ((m ^ 2).factorization q + 1), q ^ i := by
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hq2 := hqp.two_le
  have hpos : (m ^ 2).factorization q ≠ 0 := by
    have := Nat.Prime.factorization_pos_of_dvd hqp (pow_ne_zero _ hm)
      (Nat.dvd_of_mem_primeFactors hq)
    omega
  have hmem : 1 ∈ range ((m ^ 2).factorization q + 1) := Finset.mem_range.mpr (by omega)
  have := Finset.single_le_sum (f := fun i => q ^ i) (fun i _ => Nat.zero_le _) hmem
  simp only [pow_one] at this
  omega

/-- A prime factor of `m²` is odd when `m` is odd. -/
lemma prime_factor_odd {m q : ℕ} (hm : Odd m) (hq : q ∈ (m ^ 2).primeFactors) : q % 2 = 1 := by
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqm : q ∣ m ^ 2 := Nat.dvd_of_mem_primeFactors hq
  rcases hqp.eq_two_or_odd with h | h
  · subst h
    have : (2 : ℕ) ∣ m := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hqm
    rw [Nat.odd_iff] at hm
    omega
  · exact h

/-- Each local divisor sum of `m²` is odd, when `m` is odd. -/
lemma local_odd {m q : ℕ} (hm : Odd m) (hq : q ∈ (m ^ 2).primeFactors) :
    (∑ i ∈ range ((m ^ 2).factorization q + 1), q ^ i) % 2 = 1 := by
  have hqodd : q % 2 = 1 := prime_factor_odd hm hq
  have hE : (m ^ 2).factorization q = 2 * m.factorization q := by
    rw [Nat.factorization_pow]
    simp
  rw [DHP.geom_mod q ((m ^ 2).factorization q + 1) 2 (by omega), hE]
  omega

/-- The divisor sum of an odd square is odd. -/
lemma sigma_sq_odd {m : ℕ} (hm : Odd m) (hm0 : m ≠ 0) :
    (∑ x ∈ (m ^ 2).divisors, x) % 2 = 1 := by
  rw [sigma_sq_local_prod hm0, Finset.prod_nat_mod]
  rw [Finset.prod_congr rfl (fun q hq => local_odd hm hq)]
  simp

/-- **Structural core.**  In a Dris configuration there is a set `E` of primes dividing `m`,
containing all but at most `k` of them, whose local divisor sums multiply to a divisor of the
index `s`. -/
theorem exists_nonsource_subset {p k m s : ℕ} (hp : p.Prime) (hm : Odd m)
    (hpm : ¬ p ∣ m)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s)
    (h2 : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * s) :
    ∃ E : Finset ℕ, E ⊆ m.primeFactors ∧ m.primeFactors.card ≤ k + E.card ∧
      (∏ q ∈ E, ∑ i ∈ range ((m ^ 2).factorization q + 1), q ^ i) ∣ s := by
  have hp2 := hp.two_le
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero _ hm0
  -- the index is odd, hence divides `m²`, hence is prime to `p`
  have hsodd : s % 2 = 1 := by
    have hsdvd : s ∣ (∑ x ∈ (m ^ 2).divisors, x) := ⟨p ^ k, by rw [h2]; ring⟩
    have hodd := sigma_sq_odd hm hm0
    have h2s : ¬ (2 ∣ s) := by
      intro hd
      have := hd.trans hsdvd
      omega
    omega
  have hs0 : s ≠ 0 := by omega
  have hsm : s ∣ m ^ 2 := by
    have hd : s ∣ 2 * m ^ 2 := ⟨_, by rw [h1]; ring⟩
    have hcop : Nat.Coprime s 2 :=
      (((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)).symm)
    exact hcop.dvd_of_dvd_mul_left hd
  have hps : ¬ p ∣ s := by
    intro hdvd
    exact hpm (hp.dvd_of_dvd_pow (dvd_trans hdvd hsm))
  -- the local decomposition of `σ(m²)`
  set F : ℕ → ℕ := fun q => ∑ i ∈ range ((m ^ 2).factorization q + 1), q ^ i with hF
  have hprod : ∏ q ∈ (m ^ 2).primeFactors, F q = p ^ k * s := by
    rw [hF, ← sigma_sq_local_prod hm0, h2]
  have hF1 : ∀ q ∈ (m ^ 2).primeFactors, 1 < F q := fun q hq => one_lt_local hm0 hq
  classical
  set S : Finset ℕ := (m ^ 2).primeFactors.filter (fun q => p ∣ F q) with hS
  set E : Finset ℕ := (m ^ 2).primeFactors.filter (fun q => ¬ p ∣ F q) with hE
  have hcards : S.card + E.card = (m ^ 2).primeFactors.card := by
    rw [hS, hE]
    exact Finset.card_filter_add_card_filter_not _
  -- the `p`-sources: at most `k` of them
  have hSk : S.card ≤ k := by
    have hdvd : p ^ S.card ∣ ∏ q ∈ S, F q := by
      calc p ^ S.card = ∏ _q ∈ S, p := by rw [Finset.prod_const]
        _ ∣ ∏ q ∈ S, F q := by
            refine Finset.prod_dvd_prod_of_dvd _ _ ?_
            intro q hq
            exact (Finset.mem_filter.mp hq).2
    have hsub : S ⊆ (m ^ 2).primeFactors := Finset.filter_subset _ _
    have hdvd2 : p ^ S.card ∣ p ^ k * s :=
      hdvd.trans (hprod ▸ Finset.prod_dvd_prod_of_subset _ _ _ hsub)
    have hcop : Nat.Coprime (p ^ S.card) s :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hps)
    have hpk : p ^ S.card ∣ p ^ k := hcop.dvd_of_dvd_mul_right hdvd2
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hpk
  -- the remaining primes: their local divisor sums multiply to a divisor of `s`
  have hsub : E ⊆ (m ^ 2).primeFactors := Finset.filter_subset _ _
  have hdvd : (∏ q ∈ E, F q) ∣ p ^ k * s :=
    hprod ▸ Finset.prod_dvd_prod_of_subset _ _ _ hsub
  have hnp : ¬ p ∣ ∏ q ∈ E, F q := by
    intro hdvd'
    obtain ⟨q, hq, hq'⟩ := (Prime.dvd_finset_prod_iff hp.prime F).mp hdvd'
    exact (Finset.mem_filter.mp hq).2 hq'
  have hcop : Nat.Coprime (∏ q ∈ E, F q) (p ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnp).symm
  have hdvds : (∏ q ∈ E, F q) ∣ s := hcop.dvd_of_dvd_mul_left hdvd
  have hpf : (m ^ 2).primeFactors = m.primeFactors := Nat.primeFactors_pow m (by norm_num)
  refine ⟨E, ?_, ?_, hdvds⟩
  · exact hpf ▸ hsub
  · rw [← hpf]
    omega

/-- Every local divisor sum of `m²`, for `m` odd, is at least `13`. -/
lemma thirteen_le_local {m q : ℕ} (hm : Odd m) (hm0 : m ≠ 0) (hq : q ∈ (m ^ 2).primeFactors) :
    13 ≤ ∑ i ∈ range ((m ^ 2).factorization q + 1), q ^ i := by
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hq3 : 3 ≤ q := by
    have h2 := hqp.two_le
    have := prime_factor_odd hm hq
    omega
  have hE : (m ^ 2).factorization q = 2 * m.factorization q := by
    rw [Nat.factorization_pow]
    simp
  have hvpos : m.factorization q ≠ 0 := by
    have hqm : q ∣ m := by
      have : q ∣ m ^ 2 := Nat.dvd_of_mem_primeFactors hq
      exact hqp.dvd_of_dvd_pow this
    have := Nat.Prime.factorization_pos_of_dvd hqp hm0 hqm
    omega
  have hsubset : ({0, 1, 2} : Finset ℕ) ⊆ range ((m ^ 2).factorization q + 1) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    refine Finset.mem_range.mpr ?_
    omega
  have hle : ∑ i ∈ ({0, 1, 2} : Finset ℕ), q ^ i
      ≤ ∑ i ∈ range ((m ^ 2).factorization q + 1), q ^ i :=
    Finset.sum_le_sum_of_subset hsubset
  have hval : ∑ i ∈ ({0, 1, 2} : Finset ℕ), q ^ i = 1 + q + q ^ 2 := by
    norm_num [Finset.sum_insert, Finset.mem_insert]
    ring
  have hq2 : 9 ≤ q ^ 2 := by nlinarith
  omega

/-- **Main counting bound.**  For a Dris configuration `2m² = σ(p^k)·s`, `σ(m²) = p^k·s`
with `p` prime, `m` odd and `p ∤ m`, the number of distinct primes dividing `m` is at most
`k + Ω(s)`. -/
theorem omega_le_exponent_add_bigOmega_index {p k m s : ℕ} (hp : p.Prime) (hm : Odd m)
    (hpm : ¬ p ∣ m)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s)
    (h2 : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * s) :
    m.primeFactors.card ≤ k + s.primeFactorsList.length := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h1
    have : 0 < m ^ 2 := Nat.pos_of_ne_zero (pow_ne_zero _ hm0)
    omega
  obtain ⟨E, hEsub, hEcard, hEdvd⟩ := exists_nonsource_subset hp hm hpm h1 h2
  have hpf : (m ^ 2).primeFactors = m.primeFactors := Nat.primeFactors_pow m (by norm_num)
  have hone : ∀ q ∈ E, 1 < ∑ i ∈ range ((m ^ 2).factorization q + 1), q ^ i := by
    intro q hq
    exact one_lt_local hm0 (hpf ▸ hEsub hq)
  have := (card_le_bigOmega_prod _ E hone).trans (bigOmega_mono hs0 hEdvd)
  omega

/-- **Size of the index.**  In a Dris configuration, the index `s` is at least `13` to the power
of the number of primes of `m` in excess of `k`. -/
theorem pow_thirteen_le_index {p k m s : ℕ} (hp : p.Prime) (hm : Odd m)
    (hpm : ¬ p ∣ m)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s)
    (h2 : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * s) :
    13 ^ (m.primeFactors.card - k) ≤ s := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h1
    have : 0 < m ^ 2 := Nat.pos_of_ne_zero (pow_ne_zero _ hm0)
    omega
  obtain ⟨E, hEsub, hEcard, hEdvd⟩ := exists_nonsource_subset hp hm hpm h1 h2
  have hpf : (m ^ 2).primeFactors = m.primeFactors := Nat.primeFactors_pow m (by norm_num)
  have hthirteen : ∀ q ∈ E, 13 ≤ ∑ i ∈ range ((m ^ 2).factorization q + 1), q ^ i := by
    intro q hq
    exact thirteen_le_local hm hm0 (hpf ▸ hEsub hq)
  have hpow : 13 ^ E.card ≤ ∏ q ∈ E, ∑ i ∈ range ((m ^ 2).factorization q + 1), q ^ i :=
    Finset.pow_card_le_prod E _ 13 hthirteen
  have hprodle : (∏ q ∈ E, ∑ i ∈ range ((m ^ 2).factorization q + 1), q ^ i) ≤ s :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hs0) hEdvd
  have hmono : (13 : ℕ) ^ (m.primeFactors.card - k) ≤ 13 ^ E.card :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- With Sylvester's bound `ω(N) ≥ 5` (a hypothesis here), the odd part `m` of a Dris
configuration has at least four distinct prime factors. -/
theorem four_le_omega_of_sylvester {p k m s : ℕ}
    (hsylvester : ∀ n : ℕ, Nat.Perfect n → Odd n → 5 ≤ n.primeFactors.card)
    (hp : p.Prime) (hk : k ≠ 0) (hm : Odd m) (hpm : ¬ p ∣ m)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s)
    (h2 : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * s) :
    4 ≤ m.primeFactors.card := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hp2 := hp.two_le
  have hsodd : s % 2 = 1 := by
    have hsdvd : s ∣ (∑ x ∈ (m ^ 2).divisors, x) := ⟨p ^ k, by rw [h2]; ring⟩
    have hodd := sigma_sq_odd hm hm0
    have h2s : ¬ (2 ∣ s) := by
      intro hd
      have := hd.trans hsdvd
      omega
    omega
  -- `p` is odd: otherwise `σ(p^k)` is odd, while `2m² = σ(p^k)·s` is even with `s` odd
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · subst h
      have hgeom : (∑ d ∈ ((2 : ℕ) ^ k).divisors, d) = ∑ i ∈ range (k + 1), 2 ^ i :=
        DHP.sigma_prime_pow 2 k Nat.prime_two
      have hodd : (∑ i ∈ range (k + 1), (2 : ℕ) ^ i) % 2 = 1 := by
        rw [DHP.geom_succ]
        omega
      rw [hgeom] at h1
      have hmul : ((∑ i ∈ range (k + 1), (2 : ℕ) ^ i) * s) % 2 = 1 := by
        rw [Nat.mul_mod, hodd, hsodd]
      omega
    · exact h
  -- `N = p^k m²` is an odd perfect number
  have hcop : Nat.Coprime (p ^ k) (m ^ 2) :=
    Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)
  have hNpos : 0 < p ^ k * m ^ 2 := by
    have : 0 < m := Nat.pos_of_ne_zero hm0
    positivity
  have hNperfect : Nat.Perfect (p ^ k * m ^ 2) := by
    rw [Nat.perfect_iff_sum_divisors_eq_two_mul hNpos, hcop.sum_divisors_mul, h2]
    rw [show (∑ d ∈ (p ^ k).divisors, d) * (p ^ k * s)
        = ((∑ d ∈ (p ^ k).divisors, d) * s) * p ^ k by ring, ← h1]
    ring
  have hNodd : Odd (p ^ k * m ^ 2) := ((Nat.odd_iff.mpr hpodd).pow).mul hm.pow
  have hNfac : (p ^ k * m ^ 2).primeFactors = {p} ∪ m.primeFactors := by
    rw [Nat.primeFactors_mul (by positivity) (by positivity),
      Nat.primeFactors_pow p hk, Nat.primeFactors_pow m (by norm_num), hp.primeFactors]
  have hle : (p ^ k * m ^ 2).primeFactors.card ≤ 1 + m.primeFactors.card := by
    rw [hNfac]
    have := Finset.card_union_le ({p} : Finset ℕ) m.primeFactors
    simpa using this
  have hsyl := hsylvester _ hNperfect hNodd
  omega

/-- With Sylvester's bound `ω(N) ≥ 5` (a hypothesis here), every Dris configuration satisfies
`k + Ω(s) ≥ 4`. -/
theorem four_le_exponent_add_bigOmega_index {p k m s : ℕ}
    (hsylvester : ∀ n : ℕ, Nat.Perfect n → Odd n → 5 ≤ n.primeFactors.card)
    (hp : p.Prime) (hk : k ≠ 0) (hm : Odd m) (hpm : ¬ p ∣ m)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s)
    (h2 : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * s) :
    4 ≤ k + s.primeFactorsList.length := by
  have h4 := four_le_omega_of_sylvester hsylvester hp hk hm hpm h1 h2
  have hcount := omega_le_exponent_add_bigOmega_index hp hm hpm h1 h2
  omega

/-- **The Dris index at the special exponent `k = 1`.**  With Sylvester's bound `ω(N) ≥ 5`
(a hypothesis here), a Dris configuration with `k = 1` has an index `s` with at least three
prime factors counted with multiplicity. -/
theorem three_le_bigOmega_index_of_k_one {p m s : ℕ}
    (hsylvester : ∀ n : ℕ, Nat.Perfect n → Odd n → 5 ≤ n.primeFactors.card)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (h1 : 2 * m ^ 2 = (∑ d ∈ p.divisors, d) * s)
    (h2 : (∑ x ∈ (m ^ 2).divisors, x) = p * s) :
    3 ≤ s.primeFactorsList.length := by
  have h1' : 2 * m ^ 2 = (∑ d ∈ (p ^ 1).divisors, d) * s := by rwa [pow_one]
  have h2' : (∑ x ∈ (m ^ 2).divisors, x) = p ^ 1 * s := by rwa [pow_one]
  have := four_le_exponent_add_bigOmega_index hsylvester hp (k := 1) (by norm_num) hm hpm h1' h2'
  omega

/-- **The Dris index at `k = 1` is large.**  With Sylvester's bound `ω(N) ≥ 5` (a hypothesis
here), a Dris configuration with `k = 1` has `s ≥ 13³ = 2197`. -/
theorem index_ge_of_k_one {p m s : ℕ}
    (hsylvester : ∀ n : ℕ, Nat.Perfect n → Odd n → 5 ≤ n.primeFactors.card)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (h1 : 2 * m ^ 2 = (∑ d ∈ p.divisors, d) * s)
    (h2 : (∑ x ∈ (m ^ 2).divisors, x) = p * s) :
    2197 ≤ s := by
  have h1' : 2 * m ^ 2 = (∑ d ∈ (p ^ 1).divisors, d) * s := by rwa [pow_one]
  have h2' : (∑ x ∈ (m ^ 2).divisors, x) = p ^ 1 * s := by rwa [pow_one]
  have hcard : 4 ≤ m.primeFactors.card :=
    four_le_omega_of_sylvester hsylvester hp (k := 1) (by norm_num) hm hpm h1' h2'
  have hpow := pow_thirteen_le_index (k := 1) hp hm hpm h1' h2'
  have hmono : (2197 : ℕ) ≤ 13 ^ (m.primeFactors.card - 1) := by
    calc (2197 : ℕ) = 13 ^ 3 := by norm_num
      _ ≤ 13 ^ (m.primeFactors.card - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- **A lower bound for `m²` at the special exponent `k = 1`.**  With Sylvester's bound
`ω(N) ≥ 5` (a hypothesis here), a Dris configuration with `k = 1` satisfies `1098 p < m²`. -/
theorem special_prime_lt_sq_of_k_one {p m s : ℕ}
    (hsylvester : ∀ n : ℕ, Nat.Perfect n → Odd n → 5 ≤ n.primeFactors.card)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (h1 : 2 * m ^ 2 = (∑ d ∈ p.divisors, d) * s)
    (h2 : (∑ x ∈ (m ^ 2).divisors, x) = p * s) :
    1098 * p < m ^ 2 := by
  have hs := index_ge_of_k_one hsylvester hp hm hpm h1 h2
  have hsig : (∑ d ∈ p.divisors, d) = 1 + p := by
    have := DHP.sigma_prime_pow p 1 hp
    rw [pow_one] at this
    rw [this]
    simp [Finset.sum_range_succ]
  rw [hsig] at h1
  nlinarith [hp.two_le]


end DrisSupport


namespace DrisSquareIndex

/-- With a square index the first Dris relation says that `σ(p^k)` is twice a square. -/
theorem sigma_eq_two_mul_sq_of_square_index {p k m s u : ℕ} (hm : Odd m)
    (hsq : s = u ^ 2)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s)
    (h2 : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * s) :
    ∃ w : ℕ, (∑ d ∈ (p ^ k).divisors, d) = 2 * w ^ 2 := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  -- the index is odd
  have hsodd : s % 2 = 1 := by
    have hsdvd : s ∣ (∑ x ∈ (m ^ 2).divisors, x) := ⟨p ^ k, by rw [h2]; ring⟩
    have hodd := DrisSupport.sigma_sq_odd hm hm0
    have h2s : ¬ (2 ∣ s) := by
      intro hd
      have := hd.trans hsdvd
      omega
    omega
  have hs0 : s ≠ 0 := by omega
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp [hsq] at hs0
  -- the index divides `m²`, hence `u ∣ m`
  have hsm : s ∣ m ^ 2 := by
    have hd : s ∣ 2 * m ^ 2 := ⟨_, by rw [h1]; ring⟩
    have hcop : Nat.Coprime s 2 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)).symm
    exact hcop.dvd_of_dvd_mul_left hd
  have hum : u ∣ m := by
    have : u ^ 2 ∣ m ^ 2 := hsq ▸ hsm
    exact (Nat.pow_dvd_pow_iff (by norm_num)).mp this
  obtain ⟨w, hw⟩ := hum
  refine ⟨w, ?_⟩
  have hcalc : (∑ d ∈ (p ^ k).divisors, d) * u ^ 2 = (2 * w ^ 2) * u ^ 2 := by
    have hstep : (∑ d ∈ (p ^ k).divisors, d) * u ^ 2 = 2 * m ^ 2 := by rw [h1, hsq]
    rw [hstep, hw]
    ring
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero _ hu0
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hu2) hcalc

/-- **A square Dris index forces `k ≡ 1 (mod 16)` and `6 ∤ k + 1`.**  The two facts about the
equation `σ(p^k) = 2w²` are carried as hypotheses; both are proved theorems on the platform. -/
theorem square_index_exp_mod_sixteen {p k m s u : ℕ}
    (hmod16 : ∀ p k w : ℕ, p.Prime → p % 4 = 1 → k % 4 = 1 →
      (∑ d ∈ (p ^ k).divisors, d) = 2 * w ^ 2 → p % 16 = 1 ∧ k % 16 = 1)
    (hsix : ∀ p k w : ℕ, p.Prime → p ≠ 2 → (k + 1) % 6 = 0 →
      (∑ d ∈ (p ^ k).divisors, d) ≠ 2 * w ^ 2)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hm : Odd m)
    (hsq : s = u ^ 2)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s)
    (h2 : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * s) :
    p % 16 = 1 ∧ k % 16 = 1 ∧ (k + 1) % 6 ≠ 0 := by
  obtain ⟨w, hw⟩ := sigma_eq_two_mul_sq_of_square_index hm hsq h1 h2
  obtain ⟨hp16, hk16⟩ := hmod16 p k w hp hp4 hk4 hw
  refine ⟨hp16, hk16, ?_⟩
  intro hsixdvd
  exact hsix p k w hp (by omega) hsixdvd hw

/-- **No square Dris index at an exponent `k ≢ 1 (mod 16)`.**  In particular there is none at
`k = 5, 9, 13`. -/
theorem no_square_index_of_exp_ne_one_mod_sixteen {p k m s u : ℕ}
    (hmod16 : ∀ p k w : ℕ, p.Prime → p % 4 = 1 → k % 4 = 1 →
      (∑ d ∈ (p ^ k).divisors, d) = 2 * w ^ 2 → p % 16 = 1 ∧ k % 16 = 1)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk16 : k % 16 ≠ 1) (hm : Odd m)
    (hsq : s = u ^ 2)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s)
    (h2 : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * s) :
    False := by
  obtain ⟨w, hw⟩ := sigma_eq_two_mul_sq_of_square_index hm hsq h1 h2
  exact hk16 (hmod16 p k w hp hp4 hk4 hw).2

end DrisSquareIndex

theorem solution (p k m s u : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hm : Odd m)
    (hsq : s = u ^ 2)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s)
    (h2 : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * s) :
    p % 16 = 1 ∧ k % 16 = 1 ∧ (k + 1) % 6 ≠ 0 :=
  DrisSquareIndex.square_index_exp_mod_sixteen
    (fun p k w hp hp4 hk4 hw =>
      OddPerfectNumber.prime_and_exp_mod_sixteen_of_sigma_eq_two_mul_sq p k w hp hp4 hk4 hw)
    (fun p k w hp hp2 hk6 hw =>
      OddPerfectNumber.sigma_prime_pow_ne_two_mul_sq_of_six_dvd p k w hp hp2 hk6 hw)
    hp hp4 hk4 hm hsq h1 h2
