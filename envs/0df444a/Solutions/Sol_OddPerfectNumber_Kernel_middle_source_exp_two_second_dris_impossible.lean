-- Prove2me | solution 1 for OddPerfectNumber.Kernel.middle_source_exp_two_second_dris_impossible
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-13T18:54:00.609767+00:00
-- url     : https://prove2.me/submissions/3994f957-0651-4c58-98e2-8fd31187f58f

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.ModEq
set_option autoImplicit false

private theorem sum_divisors_multiple (k q : ℕ) (hk : 0 < k) (hq : 0 < q) :
    q * (∑ d ∈ k.divisors, d) ≤ ∑ d ∈ (k * q).divisors, d := by
  calc
    q * (∑ d ∈ k.divisors, d) = ∑ d ∈ k.divisors.image (fun d => q * d), d := by
      rw [Finset.sum_image]
      · exact Finset.mul_sum _ _ _
      · exact fun _ _ _ _ h => Nat.mul_left_cancel hq h
    _ ≤ ∑ d ∈ (k * q).divisors, d := by
      apply Finset.sum_le_sum_of_subset
      exact fun x hx => match Finset.mem_image.mp hx with
        | ⟨d, hd, he⟩ => he ▸ Nat.mem_divisors.mpr
          ⟨Nat.mul_comm q k ▸ Nat.mul_dvd_mul (dvd_refl q)
            (Nat.mem_divisors.mp hd).1, mul_ne_zero hk.ne' hq.ne'⟩


private theorem fixed_sigma :
    (∑ d ∈ (651 ^ 2 : ℕ).divisors, d) = 735813 := by
  rw [show (651 : ℕ) ^ 2 = 3 ^ 2 * 7 ^ 2 * 31 ^ 2 from by decide]
  rw [(show Nat.Coprime (3 ^ 2 * 7 ^ 2) (31 ^ 2) from by decide).sum_divisors_mul,
      (show Nat.Coprime (3 ^ 2) (7 ^ 2) from by decide).sum_divisors_mul,
      Nat.sum_divisors_prime_pow (show Nat.Prime 3 from by decide),
      Nat.sum_divisors_prime_pow (show Nat.Prime 7 from by decide),
      Nat.sum_divisors_prime_pow (show Nat.Prime 31 from by decide)]
  decide

theorem solution (p m d1 qC qD a b u : Nat)
    (hp : p.Prime) (hd1 : 0 < d1)
    (hu : p + 1 = 6 * u ^ 2)
    (hC : p ^ 2 + p + 1 = qC * a ^ 2)
    (hD : p ^ 2 - p + 1 = 3 * (qD * b ^ 2))
    (hqC : qC.Prime) (hqD : qD.Prime)
    (hqCmod : qC % p = 1)
    (hm : m = 3 * u * a * b * d1 * qC * qD)
    (he : m.factorization qC = 2)
    (hsource : p ∣ ∑ i ∈ Finset.range (2 * m.factorization qC + 1), qC ^ i)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (qC * qD))) :
    False := by
  have hq : qC ≡ 1 [MOD p] := hqCmod.trans (Nat.mod_eq_of_lt hp.one_lt).symm
  have hsum : (∑ i ∈ Finset.range 5, qC ^ i) ≡ 5 [MOD p] := by
    simpa using Nat.ModEq.sum (s := Finset.range 5) (fun i _ => hq.pow i)
  have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp
    ((hsum.dvd_iff (dvd_refl p)).mp (by simpa [he] using hsource))
  subst p
  have hqC31 : qC = 31 := (Nat.prime_dvd_prime_iff_eq hqC (by decide)).mp ⟨a ^ 2, hC⟩
  have hqD7 : qD = 7 := (Nat.prime_dvd_prime_iff_eq hqD (by decide)).mp
    ⟨b ^ 2, Nat.mul_left_cancel (by decide : 0 < 3) hD⟩
  subst qC qD
  have hones : u = 1 ∧ a = 1 ∧ b = 1 :=
    ⟨Nat.pow_left_injective (by decide : 2 ≠ 0)
        (Nat.mul_left_cancel (by decide : 0 < 6) hu).symm,
      Nat.pow_left_injective (by decide : 2 ≠ 0)
        (Nat.mul_left_cancel (by decide : 0 < 31) hC).symm,
      Nat.pow_left_injective (by decide : 2 ≠ 0)
        (Nat.mul_left_cancel (by decide : 0 < 7)
          (Nat.mul_left_cancel (by decide : 0 < 3) hD)).symm⟩
  rcases hones with ⟨rfl, rfl, rfl⟩
  have hms : m = 651 * d1 := by omega
  have hd1sq : 0 < d1 ^ 2 := pow_pos hd1 2
  have hlower := sum_divisors_multiple (651 ^ 2) (d1 ^ 2) (by decide) hd1sq
  rw [fixed_sigma, ← mul_pow, ← hms, h2] at hlower
  omega
