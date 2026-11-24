-- Prove2me | solution 1 for Poly1305.pocklington
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-24T08:05:57.886842+00:00
-- url     : https://prove2.me/submissions/a928a35f-f910-457e-84eb-fd11a7206db0

import Theorems.Thm_LL_Decomp126b_pocklington_divisors

section
section
namespace Poly1305.PrimePart

theorem pocklington_dev (N F a : ℕ) (hN : 1 < N) (hF : F ∣ N - 1) (hFN : N < F ^ 2)
    (ha : N ∣ a ^ (N - 1) - 1)
    (hq : ∀ q : ℕ, q.Prime → q ∣ F → Nat.Coprime (a ^ ((N - 1) / q) - 1) N) :
    N.Prime := by
  -- F ≥ 2
  have hF2 : 2 ≤ F := by
    rcases Nat.lt_or_ge F 2 with h | h
    · interval_cases F
      · rw [Nat.zero_dvd] at hF; omega
      · simp at hFN; omega
    · exact h
  -- a ≥ 1
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · exfalso
      subst h0
      obtain ⟨q, hqp, hqF⟩ := Nat.exists_prime_and_dvd (show F ≠ 1 by omega)
      have hc := hq q hqp hqF
      have h0 : (0 : ℕ) ^ ((N - 1) / q) - 1 = 0 := by
        rcases Nat.eq_zero_or_pos ((N - 1) / q) with h | h
        · rw [h]; rfl
        · rw [zero_pow (by omega)]; simp
      rw [h0, Nat.coprime_zero_left] at hc
      omega
    · exact h0
  obtain ⟨R, hR⟩ := hF
  have hNR : N = R * F + 1 := by rw [mul_comm]; omega
  have hcast : ∀ e : ℕ, (((a ^ e - 1 : ℕ)) : ℤ) = (a : ℤ) ^ e - 1 := by
    intro e
    have : 1 ≤ a ^ e := Nat.one_le_pow _ _ ha1
    push_cast [this]
    ring
  have hmod : Int.ModEq (N : ℤ) ((a : ℤ) ^ (N - 1)) 1 := by
    apply Int.ModEq.symm
    apply (Int.modEq_iff_dvd).mpr
    rw [← hcast]
    exact Int.natCast_dvd_natCast.mpr ha
  have hgcd : ∀ p : ℕ, p.Prime → p ∣ F → Int.gcd ((a : ℤ) ^ ((N - 1) / p) - 1) N = 1 := by
    intro p hp hpF
    rw [← hcast, Int.gcd_natCast_natCast]
    exact hq p hp hpF
  have hdiv := LL_Decomp126b.pocklington_divisors (by omega) hF2 hNR hmod hgcd
  by_contra hnp
  have hmin := Nat.minFac_sq_le_self (by omega) hnp
  obtain ⟨k, hk, hk'⟩ := hdiv N.minFac (Nat.minFac_dvd N)
    (Nat.minFac_prime (by omega)).one_lt
  have : F + 1 ≤ N.minFac := by rw [hk']; nlinarith
  have : (F + 1) ^ 2 ≤ N.minFac ^ 2 := Nat.pow_le_pow_left this 2
  nlinarith

end Poly1305.PrimePart

end
end

section
open Poly1305

theorem solution (N F a : ℕ) (hN : 1 < N) (hF : F ∣ N - 1) (hFN : N < F ^ 2)
    (ha : N ∣ a ^ (N - 1) - 1)
    (hq : ∀ q : ℕ, q.Prime → q ∣ F → Nat.Coprime (a ^ ((N - 1) / q) - 1) N) :
    N.Prime := by
  apply Poly1305.PrimePart.pocklington_dev <;> assumption

end
