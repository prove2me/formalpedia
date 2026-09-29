-- Prove2me | solution 1 for OddPerfectNumber.no_dris_index_three_of_one_odd_prime
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-11T08:45:59.070007+00:00
-- url     : https://prove2.me/submissions/17de0bcf-963c-41b1-9d06-8d68d98e5ab5

import Mathlib
import Theorems.Thm_OddPerfectNumber_sylvester_five_distinct_prime_factors

/-!
Solution to `OddPerfectNumber.no_dris_index_three_of_one_odd_prime`.

Sylvester's bound `ω(N) ≥ 5` is imported from the platform; everything else is developed here.
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

namespace DrisIndexThree

/-- A geometric sum of length `n + 1` is `1` modulo its base. -/
lemma geom_mod_self (q n : ℕ) (hq : 2 ≤ q) : (∑ i ∈ range (n + 1), q ^ i) % q = 1 := by
  rw [DHP.geom_succ, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- A geometric sum of length at least two exceeds `1`. -/
lemma one_lt_geom {q n : ℕ} (hq : 2 ≤ q) (hn : n ≠ 0) : 1 < ∑ i ∈ range (n + 1), q ^ i := by
  have hmem : 1 ∈ range (n + 1) := by simp; omega
  have := Finset.single_le_sum (f := fun i => q ^ i) (fun i _ => Nat.zero_le _) hmem
  simp only [pow_one] at this
  omega

/-- The divisor sum of the `q`-part of `m²` divides `σ(m²)`. -/
lemma sigma_prime_part_dvd {q m : ℕ} (hq : q.Prime) (hm0 : m ≠ 0) (hqm : q ∣ m) :
    ∃ a, a ≠ 0 ∧ (∑ i ∈ range (2 * a + 1), q ^ i) ∣ ∑ d ∈ (m ^ 2).divisors, d := by
  obtain ⟨a, w, ha, hmw, hqw⟩ := DHP.split_prime_part hq hm0 hqm
  refine ⟨a, by omega, ?_⟩
  have hcop : Nat.Coprime (q ^ (2 * a)) (w ^ 2) :=
    Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqw)
  have hm2 : m ^ 2 = q ^ (2 * a) * w ^ 2 := by rw [hmw]; ring
  rw [hm2, hcop.sum_divisors_mul, ← DHP.sigma_prime_pow q (2 * a) hq]
  exact Dvd.intro _ rfl

/-- **Main result** (with Sylvester's `ω(N) ≥ 5` as a hypothesis).
If `k + 1` has at most one odd prime divisor, the system `2m² = σ(p^k)·3`, `σ(m²) = p^k·3`
has no solution with `p` prime, `m` odd and `p ∤ m`. -/
theorem no_solution (p k m : ℕ)
    (hsylvester : ∀ n : ℕ, Nat.Perfect n → Odd n → 5 ≤ n.primeFactors.card)
    (hp : p.Prime) (hk : k ≠ 0) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hk1 : ((k + 1).primeFactors.erase 2).card ≤ 1)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * 3)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * 3) : False := by
  have hp2 := hp.two_le
  -- `m` is nonzero
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [show (0 : ℕ) ^ 2 = 0 from by norm_num, Nat.divisors_zero, Finset.sum_empty] at h2
    have : 0 < p ^ k * 3 := by positivity
    omega
  -- `σ(p^k)` as a geometric sum
  have hsig : (∑ d ∈ (p ^ k).divisors, d) = ∑ i ∈ range (k + 1), p ^ i :=
    DHP.sigma_prime_pow p k hp
  -- three divides `m`
  have h3m : 3 ∣ m := by
    have hd : 3 ∣ 2 * m ^ 2 := by rw [h1]; exact dvd_mul_left 3 _
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hd with h | h
    · omega
    · exact Nat.prime_three.dvd_of_dvd_pow h
  -- the divisor sum of the `3`-part of `m²`
  obtain ⟨c, hc0, hcdvd⟩ := sigma_prime_part_dvd Nat.prime_three hm0 h3m
  set T := ∑ i ∈ range (2 * c + 1), 3 ^ i with hT
  have hT3 : T % 3 = 1 := geom_mod_self 3 (2 * c) (by norm_num)
  have hT1 : 1 < T := one_lt_geom (q := 3) (by norm_num) (by omega)
  have hTdvd : T ∣ p ^ k * 3 := h2 ▸ hcdvd
  have hTcop3 : Nat.Coprime T 3 := by
    have : ¬ (3 ∣ T) := by omega
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr this).symm
  have hTp : T ∣ p ^ k := hTcop3.dvd_of_dvd_mul_right hTdvd
  -- `p` is neither `3` nor `2`
  have hp3 : p ≠ 3 := by
    rintro rfl
    have : Nat.Coprime T (3 ^ k) := Nat.Coprime.pow_right _ hTcop3
    exact absurd (this.eq_one_of_dvd hTp) (by omega)
  have hp2' : p ≠ 2 := by
    rintro rfl
    have hTodd : T % 2 = 1 := by
      rw [hT, DHP.geom_mod 3 (2 * c + 1) 2 (by norm_num)]
      omega
    have : Nat.Coprime T (2 ^ k) := by
      refine Nat.Coprime.pow_right _ ?_
      have : ¬ (2 ∣ T) := by omega
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr this).symm
    exact absurd (this.eq_one_of_dvd hTp) (by omega)
  have hpodd : Odd p := hp.odd_of_ne_two hp2'
  have hp5 : 5 ≤ p := by
    rcases Nat.lt_or_ge p 5 with hlt | hge
    · interval_cases p
      · exact absurd rfl hp2'
      · exact absurd rfl hp3
      · exact absurd hp (by norm_num)
    · exact hge
  -- **Key step.** A prime `q ∣ m`, `q ≠ 3`, either divides `k + 1` or has `3 ∣ σ(q^{2a})`.
  have key : ∀ q a : ℕ, q.Prime → q ≠ 3 → q ∣ m → a ≠ 0 →
      (∑ i ∈ range (2 * a + 1), q ^ i) ∣ p ^ k * 3 →
      q ∣ k + 1 ∨ 3 ∣ (∑ i ∈ range (2 * a + 1), q ^ i) := by
    intro q a hq hq3 hqm ha hdvd
    by_cases hno : 3 ∣ (∑ i ∈ range (2 * a + 1), q ^ i)
    · exact Or.inr hno
    refine Or.inl ?_
    have hq2 : q ≠ 2 := by
      rintro rfl
      rw [Nat.odd_iff] at hm
      omega
    have hcop3 : Nat.Coprime (∑ i ∈ range (2 * a + 1), q ^ i) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hno).symm
    have hdvdk : (∑ i ∈ range (2 * a + 1), q ^ i) ∣ p ^ k := hcop3.dvd_of_dvd_mul_right hdvd
    have hq2m : q ^ 2 ∣ m ^ 2 := pow_dvd_pow_of_dvd hqm 2
    have hq2S : q ^ 2 ∣ ∑ i ∈ range (k + 1), p ^ i := by
      have h3q : Nat.Coprime (q ^ 2) 3 :=
        Nat.Coprime.pow_left _ ((Nat.coprime_primes hq Nat.prime_three).mpr hq3)
      refine h3q.dvd_of_dvd_mul_right ?_
      rw [← hsig, ← h1]
      exact Dvd.dvd.mul_left hq2m 2
    exact DHP.dvd_succ_of_sigma_dvd hp hq hq2 ha hq2S hdvdk
  -- **Uniqueness.** At most one prime `q ∣ m` with `q ≠ 3` and `q ∤ k + 1`.
  have hunique : ∀ q₁ q₂ : ℕ, q₁ ∈ m.primeFactors → q₂ ∈ m.primeFactors →
      q₁ ≠ 3 → q₂ ≠ 3 → ¬ q₁ ∣ k + 1 → ¬ q₂ ∣ k + 1 → q₁ ≠ q₂ → False := by
    intro q₁ q₂ hm₁ hm₂ h₁3 h₂3 hk₁ hk₂ hne
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
    have hd₁ : (∑ i ∈ range (2 * a₁ + 1), q₁ ^ i) ∣ p ^ k * 3 := by
      rw [← h2, hsplit]; exact Dvd.intro _ rfl
    have hd₂ : (∑ i ∈ range (2 * a₂ + 1), q₂ ^ i) ∣ p ^ k * 3 := by
      rw [← h2, hsplit]
      exact Dvd.dvd.mul_left (Dvd.intro _ rfl) _
    have h3₁ := (key q₁ a₁ hq₁ h₁3 hq₁m (by omega) hd₁).resolve_left hk₁
    have h3₂ := (key q₂ a₂ hq₂ h₂3 hq₂m (by omega) hd₂).resolve_left hk₂
    have h9 : 9 ∣ p ^ k * 3 := by
      rw [← h2, hsplit]
      obtain ⟨c₁, hc₁⟩ := h3₁
      obtain ⟨c₂, hc₂⟩ := h3₂
      rw [hc₁, hc₂]
      exact ⟨c₁ * (c₂ * (∑ d ∈ (u ^ 2).divisors, d)), by ring⟩
    have h3p : 3 ∣ p ^ k := by
      have : 3 * 3 ∣ 3 * p ^ k := by
        rw [show (3 : ℕ) * 3 = 9 by norm_num, mul_comm 3 (p ^ k)]
        exact h9
      exact (mul_dvd_mul_iff_left (by norm_num : (3 : ℕ) ≠ 0)).mp this
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h3p)).symm
  -- `m` has at most three distinct prime factors
  set K : Finset ℕ := insert 3 ((k + 1).primeFactors.erase 2) with hK
  have hKcard : K.card ≤ 2 := by
    rw [hK]
    have := Finset.card_insert_le 3 ((k + 1).primeFactors.erase 2)
    omega
  have hEcard : (m.primeFactors \ K).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro q₁ hq₁ q₂ hq₂
    by_contra hne
    have hmem : ∀ q ∈ m.primeFactors \ K, q ∈ m.primeFactors ∧ q ≠ 3 ∧ ¬ q ∣ k + 1 := by
      intro q hq
      have hqm := Finset.mem_sdiff.mp hq
      refine ⟨hqm.1, ?_, ?_⟩
      · intro h3
        exact hqm.2 (by rw [hK, h3]; exact Finset.mem_insert_self _ _)
      · intro hdvd
        have hqp : q.Prime := Nat.prime_of_mem_primeFactors hqm.1
        have hq2 : q ≠ 2 := by
          rintro rfl
          have h2m : (2 : ℕ) ∣ m := Nat.dvd_of_mem_primeFactors hqm.1
          rw [Nat.odd_iff] at hm
          omega
        refine hqm.2 ?_
        rw [hK]
        exact Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨hq2, Nat.mem_primeFactors.mpr ⟨hqp, hdvd, by omega⟩⟩)
    obtain ⟨hm₁, h₁3, hk₁⟩ := hmem q₁ hq₁
    obtain ⟨hm₂, h₂3, hk₂⟩ := hmem q₂ hq₂
    exact hunique q₁ q₂ hm₁ hm₂ h₁3 h₂3 hk₁ hk₂ hne
  have hmcard : m.primeFactors.card ≤ 3 := by
    have hsub : m.primeFactors ⊆ K ∪ (m.primeFactors \ K) := by
      intro x hx
      by_cases h : x ∈ K
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, h⟩)
    have := Finset.card_le_card hsub
    have hle := Finset.card_union_le K (m.primeFactors \ K)
    omega
  -- `N = p^k m²` is an odd perfect number with at most four prime factors
  have hcop : Nat.Coprime (p ^ k) (m ^ 2) :=
    Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)
  have hNpos : 0 < p ^ k * m ^ 2 := by
    have : 0 < m := Nat.pos_of_ne_zero hm0
    positivity
  have hNperfect : Nat.Perfect (p ^ k * m ^ 2) := by
    rw [Nat.perfect_iff_sum_divisors_eq_two_mul hNpos, hcop.sum_divisors_mul, h2]
    rw [show (∑ d ∈ (p ^ k).divisors, d) * (p ^ k * 3)
        = ((∑ d ∈ (p ^ k).divisors, d) * 3) * p ^ k by ring, ← h1]
    ring
  have hNodd : Odd (p ^ k * m ^ 2) := (hpodd.pow).mul (hm.pow)
  have hNfac : (p ^ k * m ^ 2).primeFactors = {p} ∪ m.primeFactors := by
    rw [Nat.primeFactors_mul (by positivity) (by positivity),
      Nat.primeFactors_pow p hk, Nat.primeFactors_pow m (by norm_num), hp.primeFactors]
  have hcard : (p ^ k * m ^ 2).primeFactors.card ≤ 4 := by
    rw [hNfac]
    have := Finset.card_union_le ({p} : Finset ℕ) m.primeFactors
    simp only [Finset.card_singleton] at this
    omega
  have := hsylvester _ hNperfect hNodd
  omega

end DrisIndexThree

theorem solution (p k m : Nat)
    (hp : p.Prime) (hk : k ≠ 0) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hk1 : ((k + 1).primeFactors.erase 2).card ≤ 1) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * 3 ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * 3) := by
  rintro ⟨e1, e2⟩
  exact DrisIndexThree.no_solution p k m
    OddPerfectNumber.sylvester_five_distinct_prime_factors hp hk hm hpm hk1 e1 e2
