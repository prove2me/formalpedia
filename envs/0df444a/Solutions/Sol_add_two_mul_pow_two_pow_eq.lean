-- Prove2me | solution 1 for add_two_mul_pow_two_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/430aab25-dfb3-5e32-ae0c-fc43c46add10

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_add_two_mul_pow_two_pow_eq

set_option autoImplicit false

universe u

namespace PowerEstTwo

private theorem factorization_add_two_le (m : ℕ) (hm : 3 ≤ m) : m.factorization 2 + 2 ≤ m := by
  have hdvd : 2 ^ m.factorization 2 ∣ m := Nat.ordProj_dvd m 2
  have hle : 2 ^ m.factorization 2 ≤ m := Nat.le_of_dvd (by omega) hdvd
  set v := m.factorization 2 with hv
  by_contra hcon
  push Not at hcon
  have hv1 : m - 1 ≤ v := by omega
  have h3 : 2 ^ (m - 1) ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hv1
  have h4 : m < 2 ^ (m - 1) := by
    have key : ∀ t : ℕ, t + 3 < 2 ^ (t + 2) := by
      intro t
      induction t with
      | zero => norm_num
      | succ t IH => rw [show t + 1 + 2 = (t + 2) + 1 by ring, pow_succ]; omega
    have := key (m - 3)
    rw [show m - 3 + 3 = m by omega, show m - 3 + 2 = m - 1 by omega] at this
    exact this
  omega

private theorem pow_dvd_pow_mul_choose (n m : ℕ) (hm3 : 3 ≤ m) (hmn : m ≤ 2 ^ n) :
    2 ^ (n + 2) ∣ 2 ^ m * (2 ^ n).choose m := by
  have hk := Nat.factorization_choose_prime_pow_add_factorization Nat.prime_two hmn (by omega)
  have hexp : n + 2 ≤ m + ((2 ^ n).choose m).factorization 2 := by
    have := factorization_add_two_le m hm3
    omega
  have h1 : 2 ^ (n + 2) ∣ 2 ^ (m + ((2 ^ n).choose m).factorization 2) := pow_dvd_pow 2 hexp
  rw [pow_add 2 m] at h1
  exact h1.trans (Nat.mul_dvd_mul_left _ (Nat.ordProj_dvd _ _))

private theorem four_mul_choose_two (n : ℕ) (hn : 1 ≤ n) :
    ∃ q : ℕ, 4 * (2 ^ n).choose 2 = 2 ^ (n + 1) + 2 ^ (n + 2) * q := by
  refine ⟨2 ^ (n - 1) - 1, ?_⟩
  have h2 : (2 ^ n).choose 2 * 2 = 2 ^ n * (2 ^ n - 1) := by
    have := Nat.choose_two_right (2 ^ n)
    rw [this]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have : 2 ∣ 2 ^ n * (2 ^ n - 1) := by
      exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    omega
  obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  subst hk
  rw [Nat.add_sub_cancel] at *
  have e1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have e2 : 2 ^ (k + 1 + 1) = 4 * 2 ^ k := by rw [pow_succ, pow_succ]; ring
  have e3 : 2 ^ (k + 1 + 2) = 8 * 2 ^ k := by rw [pow_succ, pow_succ, pow_succ]; ring
  rw [e1] at h2 ⊢
  rw [e2, e3]
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow

  have : 4 * (2 * 2 ^ k).choose 2 = 2 * ((2 * 2 ^ k) * (2 * 2 ^ k - 1)) := by rw [← h2]; ring
  rw [this]
  zify [h1, show 1 ≤ 2 * 2 ^ k by omega]
  ring

end PowerEstTwo

open PowerEstTwo in
theorem solution
    {A : Type u} [CommRing A] (n : ℕ) (hn : 1 ≤ n) (u v : A) :
    ∃ w : A, (u + 2 * v) ^ (2 ^ n) =
      u ^ (2 ^ n) + 2 ^ (n + 1) * (u ^ (2 ^ n - 1) * v + u ^ (2 ^ n - 2) * v ^ 2) + 2 ^ (n + 2) * w := by
  classical
  set N := 2 ^ n with hN
  have hN2 : 2 ≤ N := by
    rw [hN]
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hq : ∀ m ∈ Finset.Ico 3 (N + 1), ∃ q : ℕ, 2 ^ m * N.choose m = 2 ^ (n + 2) * q := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    exact PowerEstTwo.pow_dvd_pow_mul_choose n m hm.1 (by omega)
  choose! q hq using hq
  obtain ⟨q2, hq2⟩ := PowerEstTwo.four_mul_choose_two n hn
  refine ⟨(q2 : A) * v ^ 2 * u ^ (N - 2) + ∑ m ∈ Finset.Ico 3 (N + 1), (q m : A) * v ^ m * u ^ (N - m), ?_⟩
  rw [add_comm u, add_pow, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega),
    Finset.sum_eq_sum_Ico_succ_bot (by omega), Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  rw [show (0 : ℕ) + 1 + 1 + 1 = 3 from rfl, show (0 : ℕ) + 1 + 1 = 2 from rfl,
    show (0 : ℕ) + 1 = 1 from rfl]
  rw [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, pow_one,
    Nat.choose_one_right]

  have hsum : ∑ k ∈ Finset.Ico 3 (N + 1), ((2 : A) * v) ^ k * u ^ (N - k) * (N.choose k : A) =
      ∑ k ∈ Finset.Ico 3 (N + 1), (2 : A) ^ (n + 2) * ((q k : A) * v ^ k * u ^ (N - k)) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hcast : (2 : A) ^ m * (N.choose m : A) = (2 : A) ^ (n + 2) * (q m : A) := by
      have := congrArg (Nat.cast : ℕ → A) (hq m hm)
      push_cast at this
      exact this
    calc ((2 : A) * v) ^ m * u ^ (N - m) * (N.choose m : A)
        = ((2 : A) ^ m * (N.choose m : A)) * v ^ m * u ^ (N - m) := by rw [mul_pow]; ring
      _ = (2 : A) ^ (n + 2) * ((q m : A) * v ^ m * u ^ (N - m)) := by rw [hcast]; ring

  have h2 : ((2 : A) * v) ^ 2 * u ^ (N - 2) * (N.choose 2 : A) =
      (2 : A) ^ (n + 1) * (u ^ (N - 2) * v ^ 2) + (2 : A) ^ (n + 2) * ((q2 : A) * v ^ 2 * u ^ (N - 2)) := by
    have hcast : (4 : A) * (N.choose 2 : A) = (2 : A) ^ (n + 1) + (2 : A) ^ (n + 2) * (q2 : A) := by
      have := congrArg (Nat.cast : ℕ → A) hq2
      push_cast at this
      exact this
    calc ((2 : A) * v) ^ 2 * u ^ (N - 2) * (N.choose 2 : A)
        = ((4 : A) * (N.choose 2 : A)) * (u ^ (N - 2) * v ^ 2) := by ring
      _ = _ := by rw [hcast]; ring

  have h1 : ((2 : A) * v) * u ^ (N - 1) * (N : A) = (2 : A) ^ (n + 1) * (u ^ (N - 1) * v) := by
    rw [hN, Nat.cast_pow, Nat.cast_ofNat, pow_succ]; ring
  rw [hsum, h2, h1, mul_add ((2 : A) ^ (n + 2)), Finset.mul_sum]
  ring

end S_add_two_mul_pow_two_pow_eq
end P2MW
export P2MW.S_add_two_mul_pow_two_pow_eq (solution)
