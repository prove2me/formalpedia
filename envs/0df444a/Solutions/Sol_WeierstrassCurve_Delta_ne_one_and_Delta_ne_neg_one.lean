-- Prove2me | solution 1 for WeierstrassCurve.Delta_ne_one_and_Delta_ne_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/fe21b400-1bf2-5b20-96e6-315558fffc1f

import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Positivity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Delta_ne_one_and_Delta_ne_neg_one

namespace M4cP4TateZ

theorem exists_prime_ne_three_odd_factorization {n : ℕ} (h5 : n % 8 = 5) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 3 ∧ ¬ Even (n.factorization p) := by
  by_contra hcon
  push Not at hcon
  have hn : 0 < n := by omega
  obtain ⟨a, b, ha, hb, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos hn
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := hb.ne'

  have hfac : ∀ p : ℕ, p ≠ 3 → a.factorization p = 0 := by
    intro p hp
    by_cases hpp : p.Prime
    · have hle : a.factorization p ≤ 1 :=
        (Nat.squarefree_iff_factorization_le_one ha0).mp hsq p
      have h := hcon p hpp hp
      rw [← hab, Nat.factorization_mul (pow_ne_zero 2 hb0) ha0, Nat.factorization_pow] at h
      simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
      obtain ⟨r, hr⟩ := h
      omega
    · exact Nat.factorization_eq_zero_of_not_prime a hpp
  have ha3 : a = 3 ^ a.factorization 3 := by
    apply Nat.eq_pow_of_factorization_eq_single ha0
    ext p
    rw [Finsupp.single_apply]
    by_cases hp : p = 3
    · subst hp
      simp
    · rw [hfac p hp, if_neg (Ne.symm hp)]

  have ha13 : a = 1 ∨ a = 3 := by
    have hk := (Nat.squarefree_iff_factorization_le_one ha0).mp hsq 3
    generalize hk' : a.factorization 3 = k at hk ha3
    interval_cases k
    · exact Or.inl (by simpa using ha3)
    · exact Or.inr (by simpa using ha3)

  have hb8 : b ^ 2 % 8 = 0 ∨ b ^ 2 % 8 = 1 ∨ b ^ 2 % 8 = 4 := by
    rw [Nat.pow_mod]
    have hlt : b % 8 < 8 := Nat.mod_lt _ (by norm_num)
    generalize b % 8 = r at hlt ⊢
    interval_cases r <;> decide
  rw [← hab, Nat.mul_mod] at h5
  rcases ha13 with rfl | rfl <;> rcases hb8 with h | h | h <;> rw [h] at h5 <;> norm_num at h5

theorem false_of_Δ_eq (W : WeierstrassCurve ℤ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (hΔ : W.Δ = ε) :
    False := by
  have hε2 : ε ^ 2 = 1 := by
    rcases hε with rfl | rfl <;> norm_num
  have hc : 1728 * ε = W.c₄ ^ 3 - W.c₆ ^ 2 := hΔ ▸ W.c_relation

  have hc₄ : W.c₄ = (W.a₁ ^ 2 + 4 * W.a₂) ^ 2 - 24 * (2 * W.a₄ + W.a₁ * W.a₃) := rfl
  have hc₆ : W.c₆ = -(W.a₁ ^ 2 + 4 * W.a₂) ^ 3
      + 36 * (W.a₁ ^ 2 + 4 * W.a₂) * (2 * W.a₄ + W.a₁ * W.a₃) - 216 * (W.a₃ ^ 2 + 4 * W.a₆) := rfl
  obtain ⟨s, hs | hs⟩ := Int.even_or_odd' W.a₁
  ·
    obtain ⟨A, hA⟩ : ∃ A : ℤ, W.c₄ = 8 * A :=
      ⟨2 * (s ^ 2 + W.a₂) ^ 2 - 3 * (2 * W.a₄ + W.a₁ * W.a₃), by rw [hc₄, hs]; ring⟩
    obtain ⟨B, hB⟩ : ∃ B : ℤ, W.c₆ = 8 * B :=
      ⟨-8 * (s ^ 2 + W.a₂) ^ 3 + 18 * (s ^ 2 + W.a₂) * (2 * W.a₄ + W.a₁ * W.a₃)
        - 27 * (W.a₃ ^ 2 + 4 * W.a₆), by rw [hc₆, hs]; ring⟩
    have key : 27 * ε = 8 * A ^ 3 - B ^ 2 := by
      rw [hA, hB] at hc
      have h' : (64 : ℤ) * (27 * ε) = 64 * (8 * A ^ 3 - B ^ 2) := by linear_combination hc
      exact mul_left_cancel₀ (by norm_num) h'
    have hz := congrArg (Int.cast : ℤ → ZMod 8) key
    push_cast at hz
    have h8 : (8 : ZMod 8) = 0 := by decide
    rw [h8, zero_mul, zero_sub] at hz
    have hε8 : (ε : ZMod 8) = 1 ∨ (ε : ZMod 8) = -1 := by
      rcases hε with rfl | rfl <;> simp
    generalize (ε : ZMod 8) = e at hz hε8
    generalize (B : ZMod 8) = z at hz
    revert e z
    decide
  ·
    obtain ⟨w, hw⟩ : ∃ w : ℤ, W.c₄ = 8 * w + 1 :=
      ⟨2 * (s ^ 2 + s + W.a₂) ^ 2 + (s ^ 2 + s + W.a₂) - 3 * (2 * W.a₄ + W.a₁ * W.a₃),
        by rw [hc₄, hs]; ring⟩
    obtain ⟨N, hN⟩ : ∃ N : ℤ, N = W.c₄ - 12 * ε := ⟨_, rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = W.c₄ ^ 2 + 12 * ε * W.c₄ + 144 := ⟨_, rfl⟩
    have hNQ : N * Q = W.c₆ ^ 2 := by
      rw [hN, hQ]
      linear_combination (-1 : ℤ) * hc - 144 * W.c₄ * hε2
    have hQpos : 0 < Q := by
      have hQ' : Q = (W.c₄ + 6 * ε) ^ 2 + 108 := by
        rw [hQ]
        linear_combination (-36 : ℤ) * hε2
      rw [hQ']
      positivity
    have h432 : Q - N * (W.c₄ + 24 * ε) = 432 := by
      rw [hN, hQ]
      linear_combination (288 : ℤ) * hε2
    have hN5 : N % 8 = 5 := by
      rw [hN, hw]
      rcases hε with rfl | rfl <;> omega
    have hNpos : 0 < N := by
      rcases lt_trichotomy N 0 with h | h | h
      · have hneg : N * Q < 0 := mul_neg_of_neg_of_pos h hQpos
        rw [hNQ] at hneg
        exact absurd hneg (not_lt.mpr (sq_nonneg _))
      · rw [h] at hN5
        norm_num at hN5
      · exact h

    have hnN : ((N.natAbs : ℕ) : ℤ) = N := Int.natAbs_of_nonneg hNpos.le
    have hn5 : N.natAbs % 8 = 5 := by omega
    obtain ⟨p, hp, hp3, hodd⟩ := exists_prime_ne_three_odd_factorization hn5
    apply hodd
    have hnq : N.natAbs * Q.natAbs = W.c₆.natAbs ^ 2 := by
      rw [← Int.natAbs_mul, hNQ, Int.natAbs_pow]
    have hn0 : N.natAbs ≠ 0 := by omega
    have hq0 : Q.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hQpos.ne'
    by_cases hpn : p ∣ N.natAbs
    ·
      have hpq : ¬ p ∣ Q.natAbs := by
        intro hpq
        have h1 : (p : ℤ) ∣ N := Int.ofNat_dvd_left.mpr hpn
        have h2 : (p : ℤ) ∣ Q := Int.ofNat_dvd_left.mpr hpq
        have h3 : (p : ℤ) ∣ 432 := by
          rw [← h432]
          exact dvd_sub h2 (dvd_mul_of_dvd_left h1 _)
        have h4 : p ∣ 2 ^ 4 * 3 ^ 3 := by
          norm_num
          exact_mod_cast h3
        rcases (Nat.Prime.dvd_mul hp).mp h4 with h | h
        · have h2' := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
          subst h2'
          omega
        · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h))
      have hfq : (Q.natAbs).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpq
      have h := congrArg (fun m : ℕ => m.factorization p) hnq
      simp only [Nat.factorization_mul hn0 hq0, Nat.factorization_pow, Finsupp.coe_add,
        Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, hfq, add_zero] at h
      exact ⟨(W.c₆.natAbs).factorization p, by omega⟩
    · rw [Nat.factorization_eq_zero_of_not_dvd hpn]
      exact ⟨0, rfl⟩

end M4cP4TateZ

theorem solution (W : WeierstrassCurve ℤ) : W.Δ ≠ 1 ∧ W.Δ ≠ -1 :=
  ⟨fun h => M4cP4TateZ.false_of_Δ_eq W 1 (Or.inl rfl) h,
    fun h => M4cP4TateZ.false_of_Δ_eq W (-1) (Or.inr rfl) h⟩

end S_WeierstrassCurve_Delta_ne_one_and_Delta_ne_neg_one
end P2MW
export P2MW.S_WeierstrassCurve_Delta_ne_one_and_Delta_ne_neg_one (solution)
