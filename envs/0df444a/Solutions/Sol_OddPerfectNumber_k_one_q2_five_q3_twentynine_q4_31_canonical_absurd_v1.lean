-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_q4_31_canonical_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T02:09:21.974508+00:00
-- url     : https://prove2.me/submissions/98f9b009-e581-4dd8-aa07-1055a9194582

import Mathlib

set_option autoImplicit false

theorem p26908012_upper (q x N : ℕ) (h : q = x + 1) :
    (∑ i ∈ Finset.range N, q ^ i) * x + 1 = q ^ N := by
  subst h
  exact geom_sum_mul_add x N

theorem p26908012_lower (q n k : ℕ) (h : n ≤ k) :
    (∑ i ∈ Finset.range (2 * n + 1), q ^ i) * q ^ (2 * k) ≤
      (∑ i ∈ Finset.range (2 * k + 1), q ^ i) * q ^ (2 * n) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  have hsplit : ∑ i ∈ Finset.range (2 * (n + t) + 1), q ^ i =
      ∑ i ∈ Finset.range (2 * t), q ^ i +
        q ^ (2 * t) * ∑ i ∈ Finset.range (2 * n + 1), q ^ i := by
    rw [show 2 * (n + t) + 1 = 2 * t + (2 * n + 1) by ring, Finset.sum_range_add,
      Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_add]
  rw [hsplit, add_mul]
  have e : (∑ i ∈ Finset.range (2 * n + 1), q ^ i) * q ^ (2 * (n + t)) =
      q ^ (2 * t) * (∑ i ∈ Finset.range (2 * n + 1), q ^ i) * q ^ (2 * n) := by
    rw [show 2 * (n + t) = 2 * t + 2 * n by ring, pow_add]
    ring
  rw [e]
  exact Nat.le_add_left _ _

theorem p26908012_three_mod (a : ℕ) : 3 ^ (2 * a + 1) % 31 ≠ 1 := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    rcases Nat.lt_or_ge a 15 with h | h
    · interval_cases a <;> norm_num
    · have ih' := ih (a - 15) (by omega)
      have e : 3 ^ (2 * a + 1) = 3 ^ (2 * (a - 15) + 1) * 3 ^ 30 := by
        rw [← pow_add]
        congr 1
        omega
      rw [e, Nat.mul_mod]
      norm_num
      exact ih'

theorem p26908012_tnine_mod (c : ℕ) : 29 ^ (2 * c + 1) % 31 ≠ 1 := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rcases Nat.lt_or_ge c 5 with h | h
    · interval_cases c <;> norm_num
    · have ih' := ih (c - 5) (by omega)
      have e : 29 ^ (2 * c + 1) = 29 ^ (2 * (c - 5) + 1) * 29 ^ 10 := by
        rw [← pow_add]
        congr 1
        omega
      rw [e, Nat.mul_mod]
      norm_num
      exact ih'

theorem p26908012_nd3 (a : ℕ) : ¬ 31 ∣ ∑ i ∈ Finset.range (2 * a + 1), 3 ^ i := by
  intro h
  have u := p26908012_upper 3 2 (2 * a + 1) rfl
  have := p26908012_three_mod a
  obtain ⟨t, ht⟩ := h
  rw [ht] at u
  omega

theorem p26908012_nd29 (c : ℕ) : ¬ 31 ∣ ∑ i ∈ Finset.range (2 * c + 1), 29 ^ i := by
  intro h
  have u := p26908012_upper 29 28 (2 * c + 1) rfl
  have := p26908012_tnine_mod c
  obtain ⟨t, ht⟩ := h
  rw [ht] at u
  omega

theorem p26908012_nd31 (e : ℕ) : ¬ 31 ∣ ∑ i ∈ Finset.range (2 * e + 1), 31 ^ i := by
  intro h
  have u := p26908012_upper 31 30 (2 * e + 1) rfl
  rw [pow_succ] at u
  obtain ⟨t, ht⟩ := h
  rw [ht] at u
  omega

theorem p26908012_b1 (p m d P a c e sigma S3 S29 S31 : ℕ)
    (hp : p.Prime) (hP2 : 2 * P = p + 1) (hm2 : 0 < m ^ 2)
    (hprod : m ^ 2 = P * d) (hsd : sigma = p * d)
    (KF : ∀ r, r.Prime → r ∣ sigma → r ≠ p → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = 31)
    (hfac : m ^ 2 = 3 ^ (2 * a) * 25 * 29 ^ (2 * c) * 31 ^ (2 * e))
    (hsigma : sigma = S3 * 31 * S29 * S31)
    (hS3 : S3 = ∑ i ∈ Finset.range (2 * a + 1), 3 ^ i)
    (hS29 : S29 = ∑ i ∈ Finset.range (2 * c + 1), 29 ^ i)
    (hS31 : S31 = ∑ i ∈ Finset.range (2 * e + 1), 31 ^ i)
    (he : 0 < e) : False := by
  have key : sigma * (p + 1) = 2 * p * m ^ 2 := by
    rw [hsd, hprod, ← hP2]
    ring
  have hpb : 84000 * p ≤ 83607 * (p + 1) := by
    have u3 := p26908012_upper 3 2 (2 * a + 1) rfl
    have u29 := p26908012_upper 29 28 (2 * c + 1) rfl
    have u31 := p26908012_upper 31 30 (2 * e + 1) rfl
    rw [← hS3, pow_succ] at u3
    rw [← hS29, pow_succ] at u29
    rw [← hS31, pow_succ] at u31
    have i3 : S3 * 2 ≤ 3 * 3 ^ (2 * a) := by omega
    have i29 : S29 * 28 ≤ 29 * 29 ^ (2 * c) := by omega
    have i31 : S31 * 30 ≤ 31 * 31 ^ (2 * e) := by omega
    have hp3 := Nat.mul_le_mul (Nat.mul_le_mul i3 i29) i31
    have hup : sigma * 42000 ≤ 83607 * m ^ 2 := by
      rw [hsigma, hfac]
      calc S3 * 31 * S29 * S31 * 42000
          = (S3 * 2 * (S29 * 28) * (S31 * 30)) * 775 := by ring
        _ ≤ (3 * 3 ^ (2 * a) * (29 * 29 ^ (2 * c)) * (31 * 31 ^ (2 * e))) * 775 :=
            Nat.mul_le_mul_right _ hp3
        _ = 83607 * (3 ^ (2 * a) * 25 * 29 ^ (2 * c) * 31 ^ (2 * e)) := by ring
    have h1 : sigma * 42000 * (p + 1) ≤ 83607 * m ^ 2 * (p + 1) :=
      Nat.mul_le_mul_right _ hup
    have h2 : m ^ 2 * (84000 * p) ≤ m ^ 2 * (83607 * (p + 1)) := by
      calc m ^ 2 * (84000 * p) = 2 * p * m ^ 2 * 42000 := by ring
        _ = sigma * 42000 * (p + 1) := by rw [← key]; ring
        _ ≤ 83607 * m ^ 2 * (p + 1) := h1
        _ = m ^ 2 * (83607 * (p + 1)) := by ring
    exact Nat.le_of_mul_le_mul_left h2 hm2
  have hPle : P ≤ 106 := by omega
  have n3 := p26908012_nd3 a
  have n29 := p26908012_nd29 c
  have n31 := p26908012_nd31 e
  rw [← hS3] at n3
  rw [← hS29] at n29
  rw [← hS31] at n31
  have h31p : Nat.Prime 31 := by norm_num
  have nX : ¬ 31 ∣ S3 * S29 * S31 := by
    intro h
    rcases (Nat.Prime.dvd_mul h31p).1 h with h' | h'
    · rcases (Nat.Prime.dvd_mul h31p).1 h' with h'' | h''
      · exact n3 h''
      · exact n29 h''
    · exact n31 h'
  have hcop : ∀ k, Nat.Coprime (31 ^ k) (S3 * S29 * S31) := fun k =>
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd h31p).2 nX)
  have hPs : P * sigma = 31 * (P * (S3 * S29 * S31)) := by
    rw [hsigma]; ring
  have hdiv : 31 ^ (2 * e) ∣ 31 * (P * (S3 * S29 * S31)) := by
    rw [← hPs]
    have h1 : 31 ^ (2 * e) ∣ m ^ 2 := by
      rw [hfac]; exact Dvd.intro_left _ rfl
    have h2 : P * sigma = p * m ^ 2 := by
      rw [hsd, hprod]; ring
    rw [h2]
    exact h1.mul_left p
  rcases Nat.lt_or_ge e 2 with he1 | he2
  · have he' : e = 1 := by omega
    rw [he'] at hdiv
    have h31P : 31 ∣ P := by
      have h2 : 31 * 31 ∣ 31 * (P * (S3 * S29 * S31)) := by
        simpa [pow_two] using hdiv
      have h' : 31 ^ 1 ∣ P * (S3 * S29 * S31) := by
        simpa using Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
      simpa using (hcop 1).dvd_of_dvd_mul_right h'
    obtain ⟨k, hk⟩ := h31P
    have hk3 : k ≤ 3 := by omega
    have hk0 : 0 < k := by omega
    interval_cases k
    · have hp61 : p = 61 := by omega
      have hS31v : S31 = 993 := by
        rw [hS31, he']
        simp [Finset.sum_range_succ]
      have h331 : 331 ∣ sigma := by
        rw [hsigma, hS31v]
        exact Dvd.dvd.mul_left (by norm_num) _
      have := KF 331 (by norm_num) h331 (by omega)
      omega
    · have hp' : p = 123 := by omega
      rw [hp'] at hp
      norm_num at hp
    · have hp' : p = 185 := by omega
      rw [hp'] at hp
      norm_num at hp
  · have h4 : 31 ^ 4 ∣ 31 * (P * (S3 * S29 * S31)) :=
      (pow_dvd_pow 31 (by omega)).trans hdiv
    have h4' : 31 * 31 ^ 3 ∣ 31 * (P * (S3 * S29 * S31)) := by
      simpa [pow_succ] using h4
    have h3' := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h4'
    have hP3 : 31 ^ 3 ∣ P := (hcop 3).dvd_of_dvd_mul_right h3'
    have hPpos : 0 < P := by omega
    have h5 : 29791 ≤ P := by
      have := Nat.le_of_dvd hPpos hP3
      norm_num at this
      exact this
    omega

theorem p26908012_small_a (p m d P a sigma S3 : ℕ)
    (hp4 : p % 4 = 1) (hm0 : m ≠ 0) (hP2 : 2 * P = p + 1)
    (hprod : m ^ 2 = P * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = 31)
    (KF : ∀ r, r.Prime → r ∣ sigma → r ≠ p → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = 31)
    (hS3d : S3 ∣ sigma)
    (hS3 : S3 = ∑ i ∈ Finset.range (2 * a + 1), 3 ^ i)
    (ha : a = 1 ∨ a = 2) : False := by
  rcases ha with ha1 | ha2
  · have hS3v : S3 = 13 := by
      rw [hS3, ha1]
      simp [Finset.sum_range_succ]
    rw [hS3v] at hS3d
    by_cases hp13 : 13 = p
    · have hP7 : P = 7 := by omega
      have h7 : 7 ∣ m ^ 2 := ⟨d, by rw [hprod, hP7]⟩
      have h7m : 7 ∣ m := (Nat.prime_seven).dvd_of_dvd_pow h7
      have := hsupport 7 (Nat.mem_primeFactors.2 ⟨Nat.prime_seven, h7m, hm0⟩)
      omega
    · have := KF 13 (by norm_num) hS3d hp13
      omega
  · have hS3v : S3 = 121 := by
      rw [hS3, ha2]
      simp [Finset.sum_range_succ]
    rw [hS3v] at hS3d
    have h11 : 11 ∣ sigma := (Dvd.intro 11 rfl).trans hS3d
    by_cases hp11 : 11 = p
    · omega
    · have := KF 11 (by norm_num) h11 hp11
      omega

theorem p26908012_big (m a b c e sigma S3 S5 S29 S31 : ℕ)
    (hσlt : sigma < 2 * m ^ 2)
    (hfac : m ^ 2 = 3 ^ (2 * a) * 5 ^ (2 * b) * 29 ^ (2 * c) * 31 ^ (2 * e))
    (hsigma : sigma = S3 * S5 * S29 * S31)
    (hS3 : S3 = ∑ i ∈ Finset.range (2 * a + 1), 3 ^ i)
    (hS5 : S5 = ∑ i ∈ Finset.range (2 * b + 1), 5 ^ i)
    (hS29 : S29 = ∑ i ∈ Finset.range (2 * c + 1), 29 ^ i)
    (hS31 : S31 = ∑ i ∈ Finset.range (2 * e + 1), 31 ^ i)
    (ha3 : 3 ≤ a) (hb2 : 2 ≤ b) (hc : 1 ≤ c) (he : 1 ≤ e) : False := by
  have c3 : ∑ i ∈ Finset.range (2 * 3 + 1), 3 ^ i = 1093 := by
    simp [Finset.sum_range_succ]
  have c5 : ∑ i ∈ Finset.range (2 * 2 + 1), 5 ^ i = 781 := by
    simp [Finset.sum_range_succ]
  have c29 : ∑ i ∈ Finset.range (2 * 1 + 1), 29 ^ i = 871 := by
    simp [Finset.sum_range_succ]
  have c31 : ∑ i ∈ Finset.range (2 * 1 + 1), 31 ^ i = 993 := by
    simp [Finset.sum_range_succ]
  have l3 := p26908012_lower 3 3 a ha3
  have l5 := p26908012_lower 5 2 b hb2
  have l29 := p26908012_lower 29 1 c hc
  have l31 := p26908012_lower 31 1 e he
  rw [c3, ← hS3, show (3:ℕ) ^ (2 * 3) = 729 by norm_num] at l3
  rw [c5, ← hS5, show (5:ℕ) ^ (2 * 2) = 625 by norm_num] at l5
  rw [c29, ← hS29, show (29:ℕ) ^ (2 * 1) = 841 by norm_num] at l29
  rw [c31, ← hS31, show (31:ℕ) ^ (2 * 1) = 961 by norm_num] at l31
  have hpr := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul l3 l5) l29) l31
  have hlow : 738309742599 * m ^ 2 ≤ 368236580625 * sigma := by
    rw [hsigma, hfac]
    calc 738309742599 * (3 ^ (2 * a) * 5 ^ (2 * b) * 29 ^ (2 * c) * 31 ^ (2 * e))
        = 1093 * 3 ^ (2 * a) * (781 * 5 ^ (2 * b)) * (871 * 29 ^ (2 * c)) *
            (993 * 31 ^ (2 * e)) := by ring
      _ ≤ S3 * 729 * (S5 * 625) * (S29 * 841) * (S31 * 961) := hpr
      _ = 368236580625 * (S3 * S5 * S29 * S31) := by ring
  omega

theorem solution (p m d q4 a b c e sigma : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 29 < q4)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2*a)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2*b)
    (h29mem : 29 ∈ (m ^ 2).primeFactors)
    (h29exp : (m ^ 2).factorization 29 = 2*c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e)
    (hq4eq : q4 = 31) :
    False := by
  subst hq4eq
  have hm0 : m ≠ 0 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hm
    omega
  have hm2 : 0 < m ^ 2 := by positivity
  obtain ⟨P, hPdef⟩ : ∃ P, P = (p + 1) / 2 := ⟨_, rfl⟩
  rw [← hPdef] at hprod
  have hP2 : 2 * P = p + 1 := by omega
  have hsd : sigma = p * d := hglobal.trans hsig
  have hdm : d ∣ m ^ 2 := ⟨P, by rw [hprod]; ring⟩
  have KF : ∀ r, r.Prime → r ∣ sigma → r ≠ p → r = 3 ∨ r = 5 ∨ r = 29 ∨ r = 31 := by
    intro r hr hrs hrp
    rw [hsd] at hrs
    rcases (Nat.Prime.dvd_mul hr).1 hrs with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr hp).1 h) hrp
    · have hrm : r ∣ m := hr.dvd_of_dvd_pow (h.trans hdm)
      exact hsupport r (Nat.mem_primeFactors.2 ⟨hr, hrm, hm0⟩)
  have key : sigma * (p + 1) = 2 * p * m ^ 2 := by
    rw [hsd, hprod, ← hP2]
    ring
  have hσlt : sigma < 2 * m ^ 2 := by
    by_contra h
    have h' := Nat.le_of_not_lt h
    nlinarith [Nat.mul_le_mul_right (p + 1) h']
  obtain ⟨S3, hS3⟩ : ∃ S, S = ∑ i ∈ Finset.range (2*a + 1), 3 ^ i := ⟨_, rfl⟩
  obtain ⟨S5, hS5⟩ : ∃ S, S = ∑ i ∈ Finset.range (2*b + 1), 5 ^ i := ⟨_, rfl⟩
  obtain ⟨S29, hS29⟩ : ∃ S, S = ∑ i ∈ Finset.range (2*c + 1), 29 ^ i := ⟨_, rfl⟩
  obtain ⟨S31, hS31⟩ : ∃ S, S = ∑ i ∈ Finset.range (2*e + 1), 31 ^ i := ⟨_, rfl⟩
  rw [← hS3, ← hS5, ← hS29, ← hS31] at hsigma
  rcases Nat.lt_or_ge b 2 with hb1 | hb2
  · have hb' : b = 1 := by omega
    have hS5v : S5 = 31 := by
      rw [hS5, hb']
      simp [Finset.sum_range_succ]
    have hv5 : 5 ^ (2 * b) = 25 := by rw [hb']; norm_num
    rw [hv5] at hfac
    rw [hS5v] at hsigma
    exact p26908012_b1 p m d P a c e sigma S3 S29 S31 hp hP2 hm2 hprod hsd KF hfac
      hsigma hS3 hS29 hS31 he
  · rcases (show a = 1 ∨ a = 2 ∨ 3 ≤ a by omega) with ha1 | ha2 | ha3
    · exact p26908012_small_a p m d P a sigma S3 hp4 hm0 hP2 hprod hsupport KF
        ⟨S5 * S29 * S31, by rw [hsigma]; ring⟩ hS3 (Or.inl ha1)
    · exact p26908012_small_a p m d P a sigma S3 hp4 hm0 hP2 hprod hsupport KF
        ⟨S5 * S29 * S31, by rw [hsigma]; ring⟩ hS3 (Or.inr ha2)
    · exact p26908012_big m a b c e sigma S3 S5 S29 S31 hσlt hfac hsigma hS3 hS5 hS29
        hS31 ha3 hb2 hc he
