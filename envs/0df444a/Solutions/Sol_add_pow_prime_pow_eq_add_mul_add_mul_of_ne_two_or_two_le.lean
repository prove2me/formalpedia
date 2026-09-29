-- Prove2me | solution 1 for add_pow_prime_pow_eq_add_mul_add_mul_of_ne_two_or_two_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/fe19f779-d8ab-55a5-9e22-0836c618e52f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_add_pow_prime_pow_eq_add_mul_add_mul_of_ne_two_or_two_le

set_option autoImplicit false

universe u

namespace PowerEst

private theorem factorization_add_two_le (p m : ℕ) (hp : p.Prime) (hm : 3 ≤ m) :
    m.factorization p + 2 ≤ m := by
  have hdvd : p ^ m.factorization p ∣ m := Nat.ordProj_dvd m p
  have hle : p ^ m.factorization p ≤ m := Nat.le_of_dvd (by omega) hdvd
  have h2 : 2 ^ m.factorization p ≤ p ^ m.factorization p :=
    Nat.pow_le_pow_left hp.two_le _
  set v := m.factorization p with hv

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

private theorem factorization_two_le (p : ℕ) (hp : p.Prime) : (2 : ℕ).factorization p ≤ 1 := by
  have hdvd : p ^ (2 : ℕ).factorization p ∣ 2 := Nat.ordProj_dvd 2 p
  have hle : p ^ (2 : ℕ).factorization p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  by_contra hcon
  push Not at hcon
  have : p ^ 2 ≤ p ^ (2 : ℕ).factorization p := Nat.pow_le_pow_right hp.pos hcon
  have : 4 ≤ p ^ 2 := by nlinarith [hp.two_le]
  omega

private theorem factorization_two_eq_zero (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (2 : ℕ).factorization p = 0 := by
  rw [Nat.factorization_eq_zero_iff]
  right; left
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)

private theorem pow_dvd_pow_mul_choose (p : ℕ) (hp : p.Prime) (n r m : ℕ) (hr : 1 ≤ r)
    (h2 : p ≠ 2 ∨ 2 ≤ r) (hm2 : 2 ≤ m) (hmn : m ≤ p ^ n) :
    p ^ (n + r + 1) ∣ p ^ (r * m) * (p ^ n).choose m := by
  have hk := Nat.factorization_choose_prime_pow_add_factorization hp hmn (by omega)

  have hexp : n + r + 1 ≤ r * m + ((p ^ n).choose m).factorization p := by
    have hvm : m.factorization p + r + 1 ≤ r * m := by
      rcases Nat.lt_or_ge m 3 with hlt | hge
      · have hm : m = 2 := by omega
        subst hm
        rcases h2 with hp2 | hr2
        · rw [factorization_two_eq_zero p hp hp2]; omega
        · have := factorization_two_le p hp; nlinarith
      · have := factorization_add_two_le p m hp hge
        nlinarith
    omega
  calc p ^ (n + r + 1) ∣ p ^ (r * m + ((p ^ n).choose m).factorization p) :=
        pow_dvd_pow p hexp
    _ = p ^ (r * m) * p ^ ((p ^ n).choose m).factorization p := pow_add _ _ _
    _ ∣ p ^ (r * m) * (p ^ n).choose m := Nat.mul_dvd_mul_left _ (Nat.ordProj_dvd _ _)

end PowerEst

open PowerEst in
theorem solution
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime] (n r : ℕ) (hr : 1 ≤ r) (h2 : p ≠ 2 ∨ 2 ≤ r)
    (u v : A) :
    ∃ w : A, (u + (p : A) ^ r * v) ^ (p ^ n) =
      u ^ (p ^ n) + (p : A) ^ (n + r) * u ^ (p ^ n - 1) * v + (p : A) ^ (n + r + 1) * w := by
  classical
  set N := p ^ n with hN
  have hN1 : 1 ≤ N := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos

  have hq : ∀ m ∈ Finset.Ico 2 (N + 1), ∃ q : ℕ, p ^ (r * m) * N.choose m = p ^ (n + r + 1) * q := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    exact PowerEst.pow_dvd_pow_mul_choose p Fact.out n r m hr h2 hm.1 (by omega)
  choose! q hq using hq
  refine ⟨∑ m ∈ Finset.Ico 2 (N + 1), (q m : A) * v ^ m * u ^ (N - m), ?_⟩
  rw [add_comm u, add_pow, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega),
    Finset.sum_eq_sum_Ico_succ_bot (by omega)]

  rw [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, pow_one,
    Nat.choose_one_right, Finset.mul_sum]
  have h1 : ((p : A) ^ r * v) * u ^ (N - 1) * (N : A) = (p : A) ^ (n + r) * u ^ (N - 1) * v := by
    rw [hN, Nat.cast_pow, pow_add]; ring
  rw [h1, show (0 : ℕ) + 1 + 1 = 2 from rfl]
  have hsum : ∑ k ∈ Finset.Ico 2 (N + 1), ((p : A) ^ r * v) ^ k * u ^ (N - k) * (N.choose k : A) =
      ∑ k ∈ Finset.Ico 2 (N + 1), (p : A) ^ (n + r + 1) * ((q k : A) * v ^ k * u ^ (N - k)) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hqm := hq m hm
    have hcast : ((p : A) ^ r) ^ m * (N.choose m : A) = (p : A) ^ (n + r + 1) * (q m : A) := by
      rw [← pow_mul]
      have := congrArg (Nat.cast : ℕ → A) hqm
      push_cast at this
      exact this
    calc ((p : A) ^ r * v) ^ m * u ^ (N - m) * (N.choose m : A)
        = (((p : A) ^ r) ^ m * (N.choose m : A)) * v ^ m * u ^ (N - m) := by rw [mul_pow]; ring
      _ = (p : A) ^ (n + r + 1) * ((q m : A) * v ^ m * u ^ (N - m)) := by rw [hcast]; ring
  rw [hsum]
  ring

end S_add_pow_prime_pow_eq_add_mul_add_mul_of_ne_two_or_two_le
end P2MW
export P2MW.S_add_pow_prime_pow_eq_add_mul_add_mul_of_ne_two_or_two_le (solution)
