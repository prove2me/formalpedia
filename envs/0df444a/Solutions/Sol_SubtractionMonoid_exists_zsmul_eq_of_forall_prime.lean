-- Prove2me | solution 1 for SubtractionMonoid.exists_zsmul_eq_of_forall_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/1378197d-a97a-5b3d-aa32-86f4ab68861a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_SubtractionMonoid_exists_zsmul_eq_of_forall_prime

set_option Elab.async false

theorem solution {A : Type*} [SubtractionMonoid A]
    (h : ∀ p : ℕ, p.Prime → ∀ x : A, ∃ y : A, (p : ℤ) • y = x) :
    ∀ n : ℤ, n ≠ 0 → ∀ x : A, ∃ y : A, n • y = x := by
  have core : ∀ k : ℕ, k ≠ 0 → ∀ x : A, ∃ y : A, (k : ℤ) • y = x := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk x
      rcases eq_or_ne k 1 with rfl | hk1
      · exact ⟨x, by simp⟩
      · obtain ⟨p, hp, m, rfl⟩ : ∃ p, p.Prime ∧ ∃ m, k = p * m := by
          obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd hk1
          exact ⟨p, hp, hd⟩
        have hm : m ≠ 0 := fun h0 => hk (by simp [h0])
        have hmlt : m < p * m := by nlinarith [hp.one_lt, Nat.pos_of_ne_zero hm]
        obtain ⟨z, hz⟩ := h p hp x
        obtain ⟨y, hy⟩ := ih m hmlt hm z
        exact ⟨y, by rw [Nat.cast_mul, mul_zsmul, hy, hz]⟩
  intro n hn x
  have hna : n.natAbs ≠ 0 := fun h0 => hn (Int.natAbs_eq_zero.mp h0)
  rcases Int.natAbs_eq n with he | he
  · obtain ⟨y, hy⟩ := core n.natAbs hna x
    exact ⟨y, by rw [he]; exact hy⟩
  · obtain ⟨y, hy⟩ := core n.natAbs hna x
    exact ⟨-y, by rw [he, neg_zsmul, zsmul_neg, neg_neg, hy]⟩

#print axioms solution

end S_SubtractionMonoid_exists_zsmul_eq_of_forall_prime
end P2MW
export P2MW.S_SubtractionMonoid_exists_zsmul_eq_of_forall_prime (solution)
