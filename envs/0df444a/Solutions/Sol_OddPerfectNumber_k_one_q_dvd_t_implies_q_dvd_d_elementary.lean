-- Prove2me | solution 1 for OddPerfectNumber.k_one_q_dvd_t_implies_q_dvd_d_elementary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T11:55:40.966871+00:00
-- url     : https://prove2.me/submissions/2e3822f2-827a-47b3-b70a-14e4c2125c87

import Mathlib

/-- Elementary transfer in the k = 1 unique-source configuration: `q ∣ (p + 1) / 2`
already forces `q ∣ d`. The proof only uses the `ordProj`/`ordCompl` factorization API
and multiplicativity of the divisor-sum function. -/
theorem solution (p m d q : Nat)
    (hp : p.Prime)
    (hp4 : p % 4 = 1)
    (hdvd : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hprime : q.Prime)
    (hqodd : Odd q)
    (hqdvd :
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i)
    (hqt : q ∣ (p + 1) / 2) :
    q ∣ d := by
  by_contra hnqd
  -- A. nonzero and positivity facts
  have hpge : 2 ≤ p := hp.two_le
  have htpos : 0 < (p + 1) / 2 := by
    have := hp.two_le
    omega
  have ht0 : (p + 1) / 2 ≠ 0 := htpos.ne'
  have hd0 : d ≠ 0 := fun hd => hnqd (hd ▸ dvd_zero q)
  have hm20 : m ^ 2 ≠ 0 := by
    rw [hdvd]
    exact mul_ne_zero ht0 hd0
  -- B. strip off the `q`-primary part
  set M : Nat := (m ^ 2) / q ^ (m ^ 2).factorization q with hM
  set T : Nat := ((p + 1) / 2) / q ^ ((p + 1) / 2).factorization q with hT
  have hMpos : 0 < M := by
    rw [hM]
    exact Nat.ordCompl_pos q hm20
  have hTpos : 0 < T := by
    rw [hT]
    exact Nat.ordCompl_pos q ht0
  have hM_eq : M = T * d := by
    rw [hM, hT, hdvd, Nat.ordCompl_mul ((p + 1) / 2) d q,
      (Nat.ordCompl_eq_self_iff_zero_or_not_dvd d (p := q) hprime).mpr (Or.inr hnqd)]
  have hQM_eq : q ^ (m ^ 2).factorization q * M = m ^ 2 := by
    rw [hM]
    exact Nat.ordProj_mul_ordCompl_eq_self (m ^ 2) q
  have hQM_coprime : Nat.Coprime (q ^ (m ^ 2).factorization q) M := by
    rcases Nat.eq_zero_or_pos ((m ^ 2).factorization q) with h0 | hpos
    · rw [h0, pow_zero]
      exact Nat.coprime_one_left M
    · rw [hM]
      exact (Nat.coprime_pow_left_iff hpos q _).mpr (Nat.coprime_ordCompl hprime hm20)
  -- C. `hqdvd` is a statement about the divisor sum of `q ^ a`
  have hQsum : (∑ x ∈ (q ^ (m ^ 2).factorization q).divisors, x)
      = ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i := by
    rw [← ArithmeticFunction.sigma_one_apply,
      ArithmeticFunction.sigma_one_apply_prime_pow (p := q)
        (i := (m ^ 2).factorization q) hprime]
  have hpQ : p ∣ ∑ x ∈ (q ^ (m ^ 2).factorization q).divisors, x := by
    rw [hQsum]
    exact hqdvd
  obtain ⟨u, hu⟩ := hpQ
  have hQpos : 0 < ∑ x ∈ (q ^ (m ^ 2).factorization q).divisors, x := by
    rw [← ArithmeticFunction.sigma_one_apply]
    exact (ArithmeticFunction.sigma_pos_iff).mpr (pow_pos hprime.pos _)
  have hupos : 0 < u := Nat.pos_of_mul_pos_left (hu ▸ hQpos)
  -- D. multiplicativity of the divisor sum
  have hsigma_mul : (∑ x ∈ (q ^ (m ^ 2).factorization q).divisors, x)
      * (∑ x ∈ M.divisors, x) = p * d := by
    rw [← Nat.Coprime.sum_divisors_mul hQM_coprime, hQM_eq, hsig]
  have hud : u * (∑ x ∈ M.divisors, x) = d := by
    have h1 : p * (u * (∑ x ∈ M.divisors, x)) = p * d := by
      calc p * (u * (∑ x ∈ M.divisors, x))
          = (p * u) * (∑ x ∈ M.divisors, x) := by ring
        _ = (∑ x ∈ (q ^ (m ^ 2).factorization q).divisors, x)
              * (∑ x ∈ M.divisors, x) := by rw [← hu]
        _ = p * d := hsigma_mul
    exact Nat.mul_left_cancel hp.pos h1
  -- E. master identity
  have hmaster : M = T * (u * (∑ x ∈ M.divisors, x)) := by
    calc M = T * d := hM_eq
      _ = T * (u * (∑ x ∈ M.divisors, x)) := congrArg (fun z => T * z) hud.symm
  -- F. collapse the multiplier
  have hMle : M ≤ ∑ x ∈ M.divisors, x := by
    have h := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := M)
    omega
  have hsum_le : (∑ x ∈ M.divisors, x) ≤ M := by
    conv_rhs => rw [hmaster]
    have h : (∑ x ∈ M.divisors, x) ≤ (T * u) * (∑ x ∈ M.divisors, x) :=
      Nat.le_mul_of_pos_left _ (Nat.mul_pos hTpos hupos)
    rwa [Nat.mul_assoc] at h
  have hsumM : (∑ x ∈ M.divisors, x) = M := le_antisymm hsum_le hMle
  have hTuM : T * (u * M) = M := by
    have h := hmaster
    rw [hsumM] at h
    exact h.symm
  have hTu1 : T * u = 1 := by
    have h : (T * u) * M = 1 * M := by rw [Nat.mul_assoc, hTuM, one_mul]
    exact Nat.mul_right_cancel hMpos h
  have hu1 : u = 1 := by
    have hdiv : u ∣ 1 := ⟨T, by rw [← hTu1, Nat.mul_comm]⟩
    have hle : u ≤ 1 := Nat.le_of_dvd (by norm_num) hdiv
    omega
  -- G. `p` is the geometric sum, hence `q ∣ p - 1`
  have hu' : (∑ x ∈ (q ^ (m ^ 2).factorization q).divisors, x) = p := by
    rw [hu, hu1, mul_one]
  have hpQsum : p = ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i := by
    rw [← hu', hQsum]
  obtain ⟨R, hR⟩ : ∃ R, p = 1 + q * R := by
    refine ⟨∑ k ∈ Finset.range ((m ^ 2).factorization q), q ^ k, ?_⟩
    rw [hpQsum, Finset.sum_range_succ' (fun i => q ^ i) ((m ^ 2).factorization q),
      pow_zero, Finset.mul_sum]
    have hcongr : (∑ x ∈ Finset.range ((m ^ 2).factorization q), q * q ^ x)
        = ∑ x ∈ Finset.range ((m ^ 2).factorization q), q ^ (x + 1) :=
      Finset.sum_congr rfl (fun x _ => (pow_succ' q x).symm)
    rw [hcongr, add_comm]
  have hqminus : q ∣ p - 1 := by
    rw [hR]
    have hsub : (1 + q * R) - 1 = q * R := by omega
    rw [hsub]
    exact Nat.dvd_mul_right q R
  -- H. `q ∣ p + 1`
  have h2t : 2 * ((p + 1) / 2) = p + 1 := by omega
  have hqplus : q ∣ p + 1 := by
    rw [← h2t]
    obtain ⟨c, hc⟩ := hqt
    exact ⟨c * 2, by rw [hc]; ring⟩
  -- I. `q ∣ 2` contradicts `q` odd
  have hq2 : q ∣ 2 := by
    have h := Nat.dvd_sub hqplus hqminus
    have hsub : (p + 1) - (p - 1) = 2 := by omega
    simpa [hsub] using h
  have hqle : q ≤ 2 := Nat.le_of_dvd (by norm_num) hq2
  have hqeq : q = 2 := by
    have := hprime.two_le
    omega
  have hnotodd : ¬ Odd q := by
    rw [hqeq]
    intro h
    obtain ⟨k, hk⟩ := h
    omega
  exact hnotodd hqodd
