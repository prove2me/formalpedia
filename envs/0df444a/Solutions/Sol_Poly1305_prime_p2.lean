-- Prove2me | solution 1 for Poly1305.prime_p2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-24T08:05:58.087643+00:00
-- url     : https://prove2.me/submissions/3a157112-8a6f-4b96-a481-2bfc6dc94a18

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.NormNum.Prime
import Theorems.Thm_Poly1305_pocklington
import Definitions.Def_Poly1305Bernstein

section
section
namespace Poly1305.PrimePart

/-- Binary modular exponentiation by structural recursion on a fuel bound `k`:
`pmAux n k b e = b ^ e % n` whenever `e < 2 ^ k`. Kernel-reducible. -/
def pmAux (n : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1 % n
  | k + 1, b, e =>
    if e % 2 = 0 then pmAux n k (b * b % n) (e / 2)
    else b * pmAux n k (b * b % n) (e / 2) % n

theorem pmAux_eq (n : ℕ) : ∀ k b e, e < 2 ^ k → pmAux n k b e = b ^ e % n := by
  intro k
  induction k with
  | zero =>
    intro b e he
    have : e = 0 := by simpa using he
    subst this; simp [pmAux]
  | succ k ih =>
    intro b e he
    have he2 : e / 2 < 2 ^ k := by rw [pow_succ] at he; omega
    have hih : pmAux n k (b * b % n) (e / 2) = b ^ (2 * (e / 2)) % n := by
      rw [ih _ _ he2, ← Nat.pow_mod, ← pow_two, ← pow_mul]
    have hsplit : e = 2 * (e / 2) + e % 2 := (Nat.div_add_mod e 2).symm
    simp only [pmAux]
    split_ifs with h
    · rw [hih]; congr 2; omega
    · have h1 : e % 2 = 1 := by omega
      rw [hih, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← pow_succ']
      congr 2; omega

theorem dvd_pow_sub_one_of_pmAux (N a e k : ℕ) (_hN : 1 < N) (he : e < 2 ^ k)
    (h : pmAux N k a e = 1) : N ∣ a ^ e - 1 := by
  rw [pmAux_eq N k a e he] at h
  have h1 : 1 ≤ a ^ e := by
    rcases Nat.eq_zero_or_pos (a ^ e) with h0 | h0
    · rw [h0, Nat.zero_mod] at h; omega
    · exact h0
  have := Nat.div_add_mod (a ^ e) N
  rw [h] at this
  exact ⟨a ^ e / N, by omega⟩

theorem coprime_pow_sub_one_of_pmAux (N a e k : ℕ) (hN : 0 < N) (ha : 1 ≤ a) (he : e < 2 ^ k)
    (h : Nat.gcd ((pmAux N k a e + N - 1) % N) N = 1) : Nat.Coprime (a ^ e - 1) N := by
  rw [pmAux_eq N k a e he] at h
  have h1 : 1 ≤ a ^ e := Nat.one_le_pow _ _ ha
  have hmod : (a ^ e - 1) % N = (a ^ e % N + N - 1) % N := by
    have hd := Nat.div_add_mod (a ^ e) N
    have hlt := Nat.mod_lt (a ^ e) hN
    set r := a ^ e % N
    set q := a ^ e / N
    rcases Nat.eq_zero_or_pos r with hr | hr
    · have hq : 1 ≤ q := by
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · rw [h0, hr] at hd; omega
        · exact h0
      have : a ^ e - 1 = (N - 1) + N * (q - 1) := by
        rw [← hd, hr, Nat.mul_sub, mul_one]
        have : N ≤ N * q := Nat.le_mul_of_pos_right N hq
        omega
      rw [this, Nat.add_mul_mod_self_left, hr]; simp
    · have : a ^ e - 1 = (r - 1) + N * q := by omega
      have h2 : r + N - 1 = (r - 1) + N * 1 := by omega
      rw [this, h2, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left]
  unfold Nat.Coprime
  rw [Nat.gcd_comm, Nat.gcd_rec, hmod]
  exact h

end Poly1305.PrimePart

end
end

section
section
namespace Poly1305.PrimePart

theorem prime_37003 : Nat.Prime 37003 := by norm_num
theorem prime_221101 : Nat.Prime 221101 := by norm_num

theorem p2_fermat : pmAux p2 64 2 (p2 - 1) = 1 := by decide +kernel
theorem p2_gcd_37003 :
    Nat.gcd ((pmAux p2 64 2 ((p2 - 1) / 37003) + p2 - 1) % p2) p2 = 1 := by decide +kernel
theorem p2_gcd_221101 :
    Nat.gcd ((pmAux p2 64 2 ((p2 - 1) / 221101) + p2 - 1) % p2) p2 = 1 := by decide +kernel

theorem prime_p2_dev : 222890620702 ∣ p1 - 1 ∧ p2.Prime := by
  refine ⟨by decide +kernel, ?_⟩
  have hN : 1 < p2 := by decide +kernel
  have hlt : p2 - 1 < 2 ^ 64 := by decide +kernel
  apply Poly1305.pocklington p2 (37003 * 221101) 2 hN (by decide +kernel) (by decide +kernel)
    (dvd_pow_sub_one_of_pmAux p2 2 (p2 - 1) 64 hN hlt p2_fermat)
  intro q hq hqF
  rcases (Nat.Prime.dvd_mul hq).mp hqF with h | h
  · rw [(Nat.prime_dvd_prime_iff_eq hq prime_37003).mp h]
    exact coprime_pow_sub_one_of_pmAux p2 2 _ 64 (by omega) (by norm_num)
      (lt_of_le_of_lt (Nat.div_le_self _ _) hlt) p2_gcd_37003
  · rw [(Nat.prime_dvd_prime_iff_eq hq prime_221101).mp h]
    exact coprime_pow_sub_one_of_pmAux p2 2 _ 64 (by omega) (by norm_num)
      (lt_of_le_of_lt (Nat.div_le_self _ _) hlt) p2_gcd_221101

end Poly1305.PrimePart

end
end

section
open Poly1305

theorem solution : 222890620702 ∣ p1 - 1 ∧ p2.Prime := by
  apply Poly1305.PrimePart.prime_p2_dev <;> assumption

end
