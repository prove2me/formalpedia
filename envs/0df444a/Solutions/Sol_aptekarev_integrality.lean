-- Prove2me | solution 1 for aptekarev_integrality
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T15:09:31.916348+00:00
-- url     : https://prove2.me/submissions/b09b50c8-0607-4bc0-b8e4-9c3717a35313

import Mathlib

/-- Numerator coefficient `A_k = 128k³ + 40k² - 82k - 45`. -/
def v15_apt_A (k : ℤ) : ℤ := 128 * k ^ 3 + 40 * k ^ 2 - 82 * k - 45

/-- Numerator coefficient `B_k = k²(256k³ - 240k² + 64k - 7)`. -/
def v15_apt_B (k : ℤ) : ℤ := k ^ 2 * (256 * k ^ 3 - 240 * k ^ 2 + 64 * k - 7)

/-- Numerator coefficient `C_k = k²(k-1)²(16k+1)`. -/
def v15_apt_C (k : ℤ) : ℤ := k ^ 2 * (k - 1) ^ 2 * (16 * k + 1)

/-- Explicit integer cofactor in identity (1). -/
def v15_apt_K (k a b c : ℤ) : ℤ :=
  -65536 * k ^ 4 * b + 4096 * k ^ 4 * c - 4096 * k ^ 3 * c + 32768 * k ^ 2 * a
    - 16384 * k ^ 2 * b - 256 * k ^ 2 * c + 40960 * k * a - 13568 * k * b
    + 16 * k * c + 17408 * a - 12720 * b + 15 * c

/-- Explicit integer cofactor in identity (2). -/
def v15_apt_F (k a b c : ℤ) : ℤ :=
  -16384 * k ^ 4 * b + 1024 * k ^ 4 * c + 16384 * k ^ 3 * b - 2048 * k ^ 3 * c
    + 8192 * k ^ 2 * a - 5120 * k ^ 2 * b + 1024 * k ^ 2 * c + 2048 * k * a
    + 768 * k * b - 7920 * a - 45 * b

/-- Identity (1): `4096 N = 75 I + (16k-15) K`. -/
lemma v15_apt_id1 (k a b c : ℤ) :
    4096 * (v15_apt_A k * a - v15_apt_B k * b + v15_apt_C k * c)
      = 75 * (1024 * a - 2544 * b + 3 * c)
        + (16 * k - 15) * v15_apt_K k a b c := by
  simp only [v15_apt_A, v15_apt_B, v15_apt_C, v15_apt_K]
  ring

/-- Identity (2): with `m a' = N`, `m(1024a' - 2544a + 3b) = (16k+1) F`. -/
lemma v15_apt_id2 (k a b c : ℤ) :
    1024 * (v15_apt_A k * a - v15_apt_B k * b + v15_apt_C k * c)
      - 2544 * (16 * k - 15) * a + 3 * (16 * k - 15) * b
      = (16 * k + 1) * v15_apt_F k a b c := by
  simp only [v15_apt_A, v15_apt_B, v15_apt_C, v15_apt_F]
  ring

/-- The rational coefficients of the recurrence are the integer coefficients `A, B, C`. -/
lemma v15_apt_coeff (k : ℤ) (a b c : ℤ) :
    (128 * (k : ℚ) ^ 3 + 40 * (k : ℚ) ^ 2 - 82 * (k : ℚ) - 45) * (a : ℚ)
      - (k : ℚ) ^ 2 * (256 * (k : ℚ) ^ 3 - 240 * (k : ℚ) ^ 2 + 64 * (k : ℚ) - 7) * (b : ℚ)
      + (k : ℚ) ^ 2 * ((k : ℚ) - 1) ^ 2 * (16 * (k : ℚ) + 1) * (c : ℚ)
      = ((v15_apt_A k * a - v15_apt_B k * b + v15_apt_C k * c : ℤ) : ℚ) := by
  simp only [v15_apt_A, v15_apt_B, v15_apt_C]
  push_cast
  ring

/-- If a rational sequence starts at integers and satisfies the recurrence, and the
`n = 2` invariant `17 ∣ I_2` holds, then every term is an integer. -/
lemma v15_apt_integral (f : ℕ → ℚ) (f0 f1 f2 : ℤ)
    (h0 : f 0 = (f0 : ℚ)) (h1 : f 1 = (f1 : ℚ)) (h2 : f 2 = (f2 : ℚ))
    (hrec : ∀ n : ℕ, 2 ≤ n →
      (16 * (n : ℚ) - 15) * f (n + 1)
        = (128 * (n:ℚ)^3 + 40 * (n:ℚ)^2 - 82 * (n:ℚ) - 45) * f n
          - (n:ℚ)^2 * (256*(n:ℚ)^3 - 240*(n:ℚ)^2 + 64*(n:ℚ) - 7) * f (n - 1)
          + (n:ℚ)^2 * ((n:ℚ) - 1)^2 * (16*(n:ℚ) + 1) * f (n - 2))
    (hbase : (17 : ℤ) ∣ 1024 * f2 - 2544 * f1 + 3 * f0) :
    ∀ n : ℕ, ∃ a : ℤ, f n = (a : ℚ) := by
  -- invariant: integrality of three consecutive terms plus divisibility at the last index
  let Q : ℕ → Prop := fun n =>
    2 ≤ n → ∃ a b c : ℤ, f n = (a : ℚ) ∧ f (n - 1) = (b : ℚ) ∧ f (n - 2) = (c : ℚ) ∧
      (16 * (n : ℤ) - 15) ∣ 1024 * a - 2544 * b + 3 * c
  have hQ : ∀ n, Q n := by
    intro n
    refine Nat.strong_induction_on (p := Q) n ?_
    intro n ih
    rcases n with _ | _ | _ | m
    · intro h; omega
    · intro h; omega
    · intro _
      refine ⟨f2, f1, f0, h2, ?_, ?_, ?_⟩
      · simpa using h1
      · simpa using h0
      · have h17 : (16 * ((0 + 1 + 1 : ℕ) : ℤ) - 15) = 17 := by norm_num
        rw [h17]
        exact hbase
    · intro _
      -- previous invariant
      have hprev : Q (m + 2) := ih (m + 2) (by omega)
      obtain ⟨a, b, c, hfa, hfb, hfc, hdiv⟩ := hprev (by omega)
      -- integer index `k = m + 2`
      set k : ℤ := (m : ℤ) + 2 with hk
      have hk2 : (2 : ℤ) ≤ k := by rw [hk]; omega
      have hkz : ((m + 2 : ℕ) : ℤ) = k := by rw [hk]; push_cast; ring
      have hkq : ((m + 2 : ℕ) : ℚ) = (k : ℚ) := by rw [hk]; push_cast; ring
      have hdiv' : (16 * k - 15) ∣ 1024 * a - 2544 * b + 3 * c := by
        simpa [hkz] using hdiv
      -- the integer numerator
      set N : ℤ := v15_apt_A k * a - v15_apt_B k * b + v15_apt_C k * c with hNdef
      -- the recurrence gives `m * f (m+3) = N`
      have hNq : ((16 * k - 15 : ℤ) : ℚ) * f (m + 3) = (N : ℚ) := by
        have h := hrec (m + 2) (by omega)
        rw [hfa, hfb, hfc, hkq] at h
        have hL : ((16 * k - 15 : ℤ) : ℚ) = 16 * (k : ℚ) - 15 := by
          push_cast
          ring
        rw [hL, hNdef, ← v15_apt_coeff k a b c]
        simpa using h
      -- identity (1) shows `m ∣ N`
      have h4096 : (16 * k - 15) ∣ 4096 * N := by
        rw [hNdef, v15_apt_id1 k a b c]
        have h1 : (16 * k - 15) ∣ 75 * (1024 * a - 2544 * b + 3 * c) := by
          obtain ⟨q, hq⟩ := hdiv'
          exact ⟨75 * q, by rw [hq]; ring⟩
        exact dvd_add h1 ⟨v15_apt_K k a b c, rfl⟩
      have hcop1 : IsCoprime (16 * k - 15) 4096 := by
        have h16 : IsCoprime (16 * k - 15) 16 := ⟨1, -(k - 1), by ring⟩
        simpa using h16.pow_right (n := 3)
      have hdivN : (16 * k - 15) ∣ N := hcop1.dvd_of_dvd_mul_left h4096
      obtain ⟨t, ht⟩ := hdivN
      -- so `f (m+3) = t`
      have ha_ne : (16 * k - 15 : ℤ) ≠ 0 := by omega
      have haq_ne : ((16 * k - 15 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast ha_ne
      have hft : f (m + 3) = (t : ℚ) := by
        refine mul_left_cancel₀ (a := ((16 * k - 15 : ℤ) : ℚ)) haq_ne ?_
        rw [hNq, ht]
        push_cast
        ring
      -- identity (2) transfers the invariant
      have hid2 : 1024 * N - 2544 * (16 * k - 15) * a + 3 * (16 * k - 15) * b
          = (16 * k + 1) * v15_apt_F k a b c := by
        rw [hNdef]
        exact v15_apt_id2 k a b c
      have hmulJ : (16 * k - 15) * (1024 * t - 2544 * a + 3 * b)
          = (16 * k + 1) * v15_apt_F k a b c := by
        rw [← hid2, ht]
        ring
      have hcop2 : IsCoprime (16 * k + 1) (16 * k - 15) :=
        ⟨1 - k, k, by ring⟩
      have hJdiv : (16 * k + 1) ∣ 1024 * t - 2544 * a + 3 * b :=
        hcop2.dvd_of_dvd_mul_left ⟨v15_apt_F k a b c, hmulJ⟩
      -- assemble the invariant at `m+3`
      refine ⟨t, a, b, hft, ?_, ?_, ?_⟩
      · rw [show (m + 3) - 1 = m + 2 by omega]
        exact hfa
      · rw [show (m + 3) - 2 = m + 1 by omega]
        exact hfb
      · have hk3 : (16 * ((m + 3 : ℕ) : ℤ) - 15) = 16 * k + 1 := by
          rw [hk]
          push_cast
          ring
        rw [hk3]
        exact hJdiv
  intro n
  by_cases hn : 2 ≤ n
  · obtain ⟨a, b, c, hfa, -, -, -⟩ := hQ n hn
    exact ⟨a, hfa⟩
  · interval_cases n
    · exact ⟨f0, h0⟩
    · exact ⟨f1, h1⟩

theorem solution (p q : ℕ → ℚ)
    (hp : p 0 = 0 ∧ p 1 = 2 ∧ p 2 = 31)
    (hq : q 0 = 1 ∧ q 1 = 3 ∧ q 2 = 50)
    (hrecp : ∀ n : ℕ, 2 ≤ n →
      (16 * (n : ℚ) - 15) * p (n + 1)
        = (128 * (n:ℚ)^3 + 40 * (n:ℚ)^2 - 82 * (n:ℚ) - 45) * p n
          - (n:ℚ)^2 * (256*(n:ℚ)^3 - 240*(n:ℚ)^2 + 64*(n:ℚ) - 7) * p (n - 1)
          + (n:ℚ)^2 * ((n:ℚ) - 1)^2 * (16*(n:ℚ) + 1) * p (n - 2))
    (hrecq : ∀ n : ℕ, 2 ≤ n →
      (16 * (n : ℚ) - 15) * q (n + 1)
        = (128 * (n:ℚ)^3 + 40 * (n:ℚ)^2 - 82 * (n:ℚ) - 45) * q n
          - (n:ℚ)^2 * (256*(n:ℚ)^3 - 240*(n:ℚ)^2 + 64*(n:ℚ) - 7) * q (n - 1)
          + (n:ℚ)^2 * ((n:ℚ) - 1)^2 * (16*(n:ℚ) + 1) * q (n - 2)) :
    ∀ n : ℕ, (∃ a : ℤ, p n = (a : ℚ)) ∧ (∃ b : ℤ, q n = (b : ℚ)) := by
  have hpint : ∀ n : ℕ, ∃ a : ℤ, p n = (a : ℚ) :=
    v15_apt_integral p 0 2 31 (by simpa using hp.1) (by simpa using hp.2.1)
      (by simpa using hp.2.2) hrecp (by norm_num)
  have hqint : ∀ n : ℕ, ∃ b : ℤ, q n = (b : ℚ) :=
    v15_apt_integral q 1 3 50 (by simpa using hq.1) (by simpa using hq.2.1)
      (by simpa using hq.2.2) hrecq (by norm_num)
  intro n
  exact ⟨hpint n, hqint n⟩
