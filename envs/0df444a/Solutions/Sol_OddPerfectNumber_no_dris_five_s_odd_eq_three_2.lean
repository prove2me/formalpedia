-- Prove2me | solution 2 for OddPerfectNumber.no_dris_five_s_odd_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-11T08:30:15.387737+00:00
-- url     : https://prove2.me/submissions/7809bdb2-4563-406f-9cb4-ad558ffdb9c6

import Mathlib
import Theorems.Thm_OddPerfectNumber_sylvester_five_distinct_prime_factors

/-!
Solution to `OddPerfectNumber.no_dris_five_s_odd_eq_three`.

The Dris relations at special exponent `k = 5` with index `s = 3` read
`2m² = σ(p⁵)·3` and `σ(m²) = p⁵·3`.  Every prime `q ∣ m` with `q ≠ 3` whose divisor sum
`σ(q^{2a})` is a pure power of `p` must divide `k + 1 = 6` (a lifting-the-exponent argument in
the style of Dandapat-Hunsucker-Pomerance), which is impossible; hence `3 ∣ σ(q^{2a})` for
each such `q`, and since `v_3(σ(m²)) = 1` there is at most one such prime.  So
`N = p⁵m²` is an odd perfect number with at most three distinct prime factors, contradicting
Sylvester's bound `ω(N) ≥ 5`, imported from the platform.
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

namespace DrisFiveIndexThree

/-- **Main result** (with Sylvester's `ω(N) ≥ 5` as a hypothesis).
The system `2m² = σ(p⁵)·3`, `σ(m²) = p⁵·3` has no solution with `p ≡ 1 (mod 4)` prime,
`m` odd and `p ∤ m`. -/
theorem no_solution (p m : ℕ)
    (hsylvester : ∀ n : ℕ, Nat.Perfect n → Odd n → 5 ≤ n.primeFactors.card)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * 3)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * 3) : False := by
  have hp2 := hp.two_le
  have hp5 : 5 ≤ p := by omega
  have hp3 : p ≠ 3 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  -- `m` is nonzero
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [show (0 : ℕ) ^ 2 = 0 from by norm_num, Nat.divisors_zero, Finset.sum_empty] at h2
    have : 0 < p ^ 5 * 3 := by positivity
    omega
  -- `σ(p⁵)` as a geometric sum
  have hsig : (∑ d ∈ (p ^ 5).divisors, d) = ∑ i ∈ range 6, p ^ i := DHP.sigma_prime_pow p 5 hp
  -- three divides `m`
  have h3m : 3 ∣ m := by
    have h3 : (3 : ℕ).Prime := Nat.prime_three
    have hd : 3 ∣ 2 * m ^ 2 := by rw [h1]; exact dvd_mul_left 3 _
    rcases (Nat.Prime.dvd_mul h3).mp hd with h | h
    · omega
    · exact h3.dvd_of_dvd_pow h
  -- **Key step.** For a prime `q ∣ m` with `q ≠ 3`, the divisor sum `σ(q^{2a})` is divisible
  -- by `3`; otherwise it would be a pure power of `p` and `q` would divide `k + 1 = 6`.
  have key : ∀ q a : ℕ, q.Prime → q ≠ 3 → q ∣ m → a ≠ 0 →
      (∑ i ∈ range (2 * a + 1), q ^ i) ∣ p ^ 5 * 3 →
      3 ∣ (∑ i ∈ range (2 * a + 1), q ^ i) := by
    intro q a hq hq3 hqm ha hdvd
    by_contra hno
    have hq2 : q ≠ 2 := by
      rintro rfl
      rw [Nat.odd_iff] at hm
      omega
    -- `σ(q^{2a})` is coprime to `3`, hence divides `p⁵`
    have hcop3 : Nat.Coprime (∑ i ∈ range (2 * a + 1), q ^ i) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hno).symm
    have hdvd5 : (∑ i ∈ range (2 * a + 1), q ^ i) ∣ p ^ 5 :=
      (Nat.Coprime.dvd_of_dvd_mul_right hcop3 hdvd)
    -- `q²` divides `σ(p⁵)`
    have hq2m : q ^ 2 ∣ m ^ 2 := pow_dvd_pow_of_dvd hqm 2
    have hq2S : q ^ 2 ∣ ∑ i ∈ range 6, p ^ i := by
      have h3q : Nat.Coprime (q ^ 2) 3 :=
        Nat.Coprime.pow_left _ ((Nat.coprime_primes hq Nat.prime_three).mpr hq3)
      refine h3q.dvd_of_dvd_mul_right ?_
      rw [← hsig, ← h1]
      exact Dvd.dvd.mul_left hq2m 2
    have hq6 : q ∣ 5 + 1 := DHP.dvd_succ_of_sigma_dvd hp hq hq2 ha (by simpa using hq2S) hdvd5
    have hq2' := hq.two_le
    have hq6' : q ≤ 6 := Nat.le_of_dvd (by omega) hq6
    interval_cases q
    · exact hq2 rfl
    · exact hq3 rfl
    · norm_num at hq6
    · norm_num at hq6
    · exact absurd hq (by norm_num)
  -- **Uniqueness.** At most one prime other than `3` divides `m`.
  have hunique : ∀ q₁ q₂ : ℕ, q₁ ∈ m.primeFactors → q₂ ∈ m.primeFactors →
      q₁ ≠ 3 → q₂ ≠ 3 → q₁ ≠ q₂ → False := by
    intro q₁ q₂ hm₁ hm₂ h₁3 h₂3 hne
    obtain ⟨hq₁, hq₁m, -⟩ := Nat.mem_primeFactors.mp hm₁
    obtain ⟨hq₂, hq₂m, -⟩ := Nat.mem_primeFactors.mp hm₂
    obtain ⟨a₁, w, ha₁, hmw, hq₁w⟩ := DHP.split_prime_part hq₁ hm0 hq₁m
    have hw0 : w ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hmw
      exact hm0 hmw
    have hq₂w : q₂ ∣ w := by
      have hd : q₂ ∣ q₁ ^ a₁ * w := hmw ▸ hq₂m
      rcases (Nat.Prime.dvd_mul hq₂).mp hd with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq₂ hq₁).mp (hq₂.dvd_of_dvd_pow h)) hne.symm
      · exact h
    obtain ⟨a₂, u, ha₂, hwu, hq₂u⟩ := DHP.split_prime_part hq₂ hw0 hq₂w
    -- multiplicativity of `σ` on the two prime parts
    have hcop₁ : Nat.Coprime (q₁ ^ (2 * a₁)) (w ^ 2) :=
      Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd hq₁).mpr hq₁w)
    have hcop₂ : Nat.Coprime (q₂ ^ (2 * a₂)) (u ^ 2) :=
      Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd hq₂).mpr hq₂u)
    have hm2 : m ^ 2 = q₁ ^ (2 * a₁) * w ^ 2 := by rw [hmw]; ring
    have hw2 : w ^ 2 = q₂ ^ (2 * a₂) * u ^ 2 := by rw [hwu]; ring
    have hsplit : (∑ d ∈ (m ^ 2).divisors, d) =
        (∑ i ∈ range (2 * a₁ + 1), q₁ ^ i) *
          ((∑ i ∈ range (2 * a₂ + 1), q₂ ^ i) * (∑ d ∈ (u ^ 2).divisors, d)) := by
      rw [hm2, hcop₁.sum_divisors_mul, hw2, hcop₂.sum_divisors_mul,
        DHP.sigma_prime_pow q₁ (2 * a₁) hq₁, DHP.sigma_prime_pow q₂ (2 * a₂) hq₂]
    have hd₁ : (∑ i ∈ range (2 * a₁ + 1), q₁ ^ i) ∣ p ^ 5 * 3 := by
      rw [← h2, hsplit]; exact Dvd.intro _ rfl
    have hd₂ : (∑ i ∈ range (2 * a₂ + 1), q₂ ^ i) ∣ p ^ 5 * 3 := by
      rw [← h2, hsplit]
      exact Dvd.dvd.mul_left (Dvd.intro _ rfl) _
    have h3₁ := key q₁ a₁ hq₁ h₁3 hq₁m (by omega) hd₁
    have h3₂ := key q₂ a₂ hq₂ h₂3 hq₂m (by omega) hd₂
    -- `9` divides `σ(m²) = 3p⁵`
    have h9 : 9 ∣ p ^ 5 * 3 := by
      rw [← h2, hsplit]
      obtain ⟨c₁, hc₁⟩ := h3₁
      obtain ⟨c₂, hc₂⟩ := h3₂
      rw [hc₁, hc₂]
      exact ⟨c₁ * (c₂ * (∑ d ∈ (u ^ 2).divisors, d)), by ring⟩
    have h3p : 3 ∣ p ^ 5 := by
      have : 3 * 3 ∣ 3 * p ^ 5 := by
        rw [show (3 : ℕ) * 3 = 9 by norm_num, mul_comm 3 (p ^ 5)]
        exact h9
      exact (mul_dvd_mul_iff_left (by norm_num : (3 : ℕ) ≠ 0)).mp this
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h3p)).symm
  -- `m` has at most two prime factors
  have h3mem : 3 ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3m, hm0⟩
  have herase : (m.primeFactors.erase 3).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro q₁ hq₁ q₂ hq₂
    by_contra hne
    exact hunique q₁ q₂ (Finset.mem_of_mem_erase hq₁) (Finset.mem_of_mem_erase hq₂)
      (Finset.ne_of_mem_erase hq₁) (Finset.ne_of_mem_erase hq₂) hne
  have hmcard : m.primeFactors.card ≤ 2 := by
    have := Finset.card_erase_add_one h3mem
    omega
  -- `N = p⁵ m²` is an odd perfect number with at most three prime factors
  have hcop : Nat.Coprime (p ^ 5) (m ^ 2) :=
    Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)
  have hNpos : 0 < p ^ 5 * m ^ 2 := by
    have : 0 < m := Nat.pos_of_ne_zero hm0
    positivity
  have hNperfect : Nat.Perfect (p ^ 5 * m ^ 2) := by
    rw [Nat.perfect_iff_sum_divisors_eq_two_mul hNpos, hcop.sum_divisors_mul, h2]
    rw [show (∑ d ∈ (p ^ 5).divisors, d) * (p ^ 5 * 3)
        = ((∑ d ∈ (p ^ 5).divisors, d) * 3) * p ^ 5 by ring, ← h1]
    ring
  have hNodd : Odd (p ^ 5 * m ^ 2) := (hpodd.pow).mul (hm.pow)
  have hNfac : (p ^ 5 * m ^ 2).primeFactors = {p} ∪ m.primeFactors := by
    rw [Nat.primeFactors_mul (by positivity) (by positivity),
      Nat.primeFactors_pow p (by norm_num), Nat.primeFactors_pow m (by norm_num),
      hp.primeFactors]
  have hcard : (p ^ 5 * m ^ 2).primeFactors.card ≤ 3 := by
    rw [hNfac]
    have := Finset.card_union_le ({p} : Finset ℕ) m.primeFactors
    simp only [Finset.card_singleton] at this
    omega
  have := hsylvester _ hNperfect hNodd
  omega

end DrisFiveIndexThree

theorem solution (p m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hs3 : s = 3) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) := by
  subst hs3
  rintro ⟨e1, e2⟩
  exact DrisFiveIndexThree.no_solution p m
    OddPerfectNumber.sylvester_five_distinct_prime_factors hp hp4 hm hpm e1 e2
