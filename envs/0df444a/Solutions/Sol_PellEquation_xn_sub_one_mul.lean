-- Prove2me | solution 1 for PellEquation.xn_sub_one_mul
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T17:26:23.777761+00:00
-- url     : https://prove2.me/submissions/b7ab7ab6-215f-4f7f-beac-7965b2c66587

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.MR.StridePrizePell =====
section
/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# THE PRIZE'S SET BY PELL — the `r`-free roughness set from a seed, with no analytic input

`zRough_oddOmega_infinite_primorial` (`StrideGradeReceipt.lean`) concludes an `r`-FREE set:
infinitely many `n` with `n(n+2)` `z`-rough and `Ω(n(n+2))` odd, at `primorial z ≤ 548`; its class
binders `hr`, `hcop` appear only as hypotheses.  That SET is reached here by an elementary
construction (the refuter pass `wf_da4bb51d-7db`, R1's U1; the (B1) grade-12 census freeze §7.0).

THE CONSTRUCTION.  Take a seed `K` with `primorial z ∣ K` and `Ω(K² − 1)` odd, and `d := K² − 1`.
Mathlib's Pell sequences at `a = K` (`Mathlib/NumberTheory/PellMatiyasevic.lean`) solve
`x_m² − d·y_m² = 1` with `(x_1, y_1) = (K, 1)`.  Put `n := x_m − 1`, so `n(n+2) = x_m² − 1 = d·y_m²`
and `Ω(n(n+2)) = Ω(d) + 2·Ω(y_m)` is ODD.  At every ODD index `m`, `y_m` is prime to `K`:
`y_{m+2} + y_m = 2K·y_{m+1}` and `y_1 = 1` (`pell_yn_odd_not_dvd`); and `d` is prime to `K`
since `d + 1 = K²`.  A prime `p ≤ z` divides `primorial z`, hence `K`, hence neither factor.
`x_m` is strictly increasing, so the set is infinite.  The seed `K = 4620 = 2·primorial 11` has
`d = 21344399 = 31·149·4621`, `Ω(d) = 3`, and gives the set at every `z ≤ 12`
(`zRough_oddOmega_infinite_pell_4620`); its first member is `n = 4619 = 31·149`.

HONEST LABEL.  This reaches the `r`-free SET, and only through the one class
`n ≡ −1 (mod primorial z)` (at odd `m`, `x_m ≡ 0`).  It does NOT reach the per-class statement
(`n ≡ r (mod primorial z)` for every admissible `r`), which is what the stride supply
`logChowlaAffSupplyW_holds` carries and what the lane's price is quoted against.  ADDITIVE ONLY:
every name is new, no landed declaration moves, and no cap or (B1) statement is touched.
Nothing here bears on twin primes.
-/

namespace Salt.MR

open ArithmeticFunction

/-- **⟦PELL `y` AT ODD INDICES IS PRIME TO THE SEED⟧ (class B)** — for `1 < a` and a prime
`p ∣ a`, `p ∤ yn (2j+1)`.  Induction on `j`: `yn 1 = 1`, and `yn (m+2) + yn m = 2·a·yn (m+1)`
(mathlib's `Pell.yn_succ_succ`) puts `p ∣ yn (2j+3) + yn (2j+1)`, so `p ∣ yn (2j+3)` would give
`p ∣ yn (2j+1)`. -/
theorem pell_yn_odd_not_dvd {a : ℕ} (a1 : 1 < a) {p : ℕ} (hp : p.Prime) (hpa : p ∣ a) :
    ∀ j : ℕ, ¬ p ∣ Pell.yn a1 (2 * j + 1)
  | 0 => by
    intro h
    have h1 : Pell.yn a1 (2 * 0 + 1) = 1 := Pell.yn_one a1
    rw [h1] at h
    exact hp.one_lt.ne' (Nat.dvd_one.mp h)
  | j + 1 => by
    intro h
    have hrec := Pell.yn_succ_succ a1 (2 * j + 1)
    have h2 : p ∣ Pell.yn a1 (2 * j + 1 + 2) + Pell.yn a1 (2 * j + 1) := by
      rw [hrec]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hpa 2) _
    have hidx : 2 * (j + 1) + 1 = 2 * j + 1 + 2 := by ring
    rw [hidx] at h
    exact pell_yn_odd_not_dvd a1 hp hpa j ((Nat.dvd_add_right h).mp h2)

/-- **⟦THE PELL IDENTITY IN THE PRIZE'S SHAPE⟧ (class B)** —
`(x_m − 1)·((x_m − 1) + 2) = (a² − 1)·y_m²`, from mathlib's `Pell.pell_eq`
(`x_m·x_m − d·y_m·y_m = 1`, `d = a·a − 1` definitionally) and `1 ≤ x_m`. -/
theorem pell_xn_sub_one_mul {a : ℕ} (a1 : 1 < a) (m : ℕ) :
    (Pell.xn a1 m - 1) * (Pell.xn a1 m - 1 + 2)
      = (a ^ 2 - 1) * (Pell.yn a1 m * Pell.yn a1 m) := by
  have hpe : Pell.xn a1 m * Pell.xn a1 m - (a * a - 1) * Pell.yn a1 m * Pell.yn a1 m = 1 :=
    Pell.pell_eq a1 m
  have hle : (a * a - 1) * Pell.yn a1 m * Pell.yn a1 m ≤ Pell.xn a1 m * Pell.xn a1 m := by
    by_contra hlt
    rw [Nat.sub_eq_zero_of_le (not_le.mp hlt).le] at hpe
    exact absurd hpe (by norm_num)
  have hXY := (Nat.sub_eq_iff_eq_add hle).mp hpe
  have hx : 1 ≤ Pell.xn a1 m := Pell.x_pos a1 m
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hx
  have hsq : a ^ 2 - 1 = a * a - 1 := by rw [sq]
  rw [hsq, hk, Nat.add_sub_cancel_left]
  rw [hk] at hXY
  generalize a * a - 1 = D at hXY ⊢
  generalize Pell.yn a1 m = y at hXY ⊢
  nlinarith [hXY]

/-- **⟦THE PRIZE'S SET FROM A PELL SEED⟧ (class B)** — for every `z` and every seed `K` with
`primorial z ∣ K` and `Ω(K² − 1)` odd, infinitely many `n` have `n(n+2)` `z`-rough and
`Ω(n(n+2))` odd.  The members are `n = Pell.xn (2j+1) − 1` at `a = K`.  Nondegeneracy is forced
by the hypothesis: `Ω 0 = Ω 1 = 0` is even, so `1 < K`. -/
theorem zRough_oddOmega_infinite_of_pell_seed {z K : ℕ} (hPK : primorial z ∣ K)
    (hΩ : Odd (ArithmeticFunction.cardFactors (K ^ 2 - 1))) :
    {n : ℕ | (∀ p ∈ (n * (n + 2)).primeFactors, z < p)
      ∧ Odd (ArithmeticFunction.cardFactors (n * (n + 2)))}.Infinite := by
  have hK1 : 1 < K := by
    by_contra hK
    have hK' : K ≤ 1 := not_lt.mp hK
    interval_cases K <;> simp at hΩ
  have hd0 : K ^ 2 - 1 ≠ 0 := by
    intro h
    rw [h] at hΩ
    simp at hΩ
  have hd1 : K ^ 2 - 1 + 1 = K ^ 2 := Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))
  refine Set.infinite_of_injective_forall_mem (f := fun j => Pell.xn hK1 (2 * j + 1) - 1)
    (fun i j hij => ?_) (fun j => ?_)
  · have hxi := Pell.x_pos hK1 (2 * i + 1)
    have hxj := Pell.x_pos hK1 (2 * j + 1)
    have h1 : Pell.xn hK1 (2 * i + 1) = Pell.xn hK1 (2 * j + 1) := by
      simp only at hij
      omega
    have h2 := (Pell.strictMono_x hK1).injective h1
    omega
  · have hy0 : Pell.yn hK1 (2 * j + 1) ≠ 0 := by
      have h := (Pell.strictMono_y hK1) (show 0 < 2 * j + 1 by omega)
      rw [Pell.yn_zero] at h
      omega
    have hid := pell_xn_sub_one_mul hK1 (2 * j + 1)
    simp only [Set.mem_setOf_eq]
    rw [hid]
    refine ⟨fun p hp => ?_, ?_⟩
    · have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      by_contra hpz
      have hpK : p ∣ K := (hpp.dvd_primorial_iff.mpr (not_lt.mp hpz)).trans hPK
      rcases (Nat.Prime.dvd_mul hpp).mp hpd with hpd' | hpy
      · have h1 : p ∣ K ^ 2 := dvd_pow hpK two_ne_zero
        rw [← hd1] at h1
        exact hpp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hpd').mp h1))
      · rcases (Nat.Prime.dvd_mul hpp).mp hpy with h | h <;>
          exact pell_yn_odd_not_dvd hK1 hpp hpK j h
    · rw [cardFactors_mul hd0 (mul_ne_zero hy0 hy0), cardFactors_mul hy0 hy0]
      exact hΩ.add_even ⟨_, rfl⟩

/-- **⟦THE INSTANCE AT `K = 4620`⟧ (class B)** — for every `z ≤ 12`, the prize's set is infinite.
`primorial z ∣ primorial 12 = 2310 ∣ 4620`, and `4620² − 1 = 21344399 = 31·149·4621` with all
three prime, so `Ω = 3` is odd. -/
theorem zRough_oddOmega_infinite_pell_4620 {z : ℕ} (hz : z ≤ 12) :
    {n : ℕ | (∀ p ∈ (n * (n + 2)).primeFactors, z < p)
      ∧ Odd (ArithmeticFunction.cardFactors (n * (n + 2)))}.Infinite := by
  refine zRough_oddOmega_infinite_of_pell_seed (K := 4620) ?_ ?_
  · have h12 : primorial 12 = 2310 := by decide
    have h2310 : (2310 : ℕ) ∣ 4620 := ⟨2, by norm_num⟩
    exact (primorial_dvd_primorial hz).trans (h12 ▸ h2310)
  · have hfac : (4620 : ℕ) ^ 2 - 1 = 31 * 149 * 4621 := by norm_num
    have h31 : Nat.Prime 31 := by norm_num
    have h149 : Nat.Prime 149 := by norm_num
    have h4621 : Nat.Prime 4621 := by norm_num
    rw [hfac, cardFactors_mul (by norm_num) (by norm_num),
      cardFactors_mul (by norm_num) (by norm_num),
      cardFactors_apply_prime h31, cardFactors_apply_prime h149, cardFactors_apply_prime h4621]
    exact ⟨1, by norm_num⟩

end Salt.MR

end




section
open ArithmeticFunction

theorem solution {a : ℕ} (a1 : 1 < a) (m : ℕ) :
    (Pell.xn a1 m - 1) * (Pell.xn a1 m - 1 + 2)
      = (a ^ 2 - 1) * (Pell.yn a1 m * Pell.yn a1 m) := by
  apply Salt.MR.pell_xn_sub_one_mul <;> assumption

end

