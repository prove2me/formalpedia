-- Prove2me | solution 1 for OddPerfectNumber.Kernel.sq_mul_squarefree_canonical
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T09:25:17.953977+00:00
-- url     : https://prove2.me/submissions/20e99e9c-273e-41eb-af37-932de78a9873

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
--
-- The square-free decomposition of the Dris index, in the orientation the
-- cardinality machinery of this workstream expects.
--
-- `Nat.sq_mul_squarefree_of_pos {n : ℕ} (hn : 0 < n)` in the pinned revision
-- (`Mathlib/Data/Nat/Squarefree.lean:306`) produces
--
--     ∃ a b, 0 < a ∧ 0 < b ∧ b ^ 2 * a = n ∧ Squarefree a
--
-- i.e. the **square on the left** and the square-free part second.  The proved
-- children `squarefree_card_ge_three_of_not_small` (64627c09),
-- `squarefree_card_ge_two_of_not_one_or_prime` (9c90129e) and
-- `squarefree_card_two_eq_two_primes` (04aeb617) all quantify over *the
-- square-free number itself*, and the `k = 5` index exclusion
-- `five_index_not_prime_mul_square` (2ec27119) rules out `s = q * a ^ 2` for
-- `q` prime, which is the same statement as "the square-free part is not
-- prime". So the only thing missing for the `k = 5` reduction is the
-- decomposition itself, stated in the `d1 ^ 2 * d2 = s` orientation the
-- subsequent children use.
--
-- No mathematics beyond the Mathlib lemma: this is pure reorientation.
import Mathlib

namespace OddPerfectNumber.Kernel
namespace SqFree

theorem solution_aux (s : Nat) (hspos : 0 < s) :
    ∃ d1 d2 : Nat, 0 < d1 ∧ 0 < d2 ∧ d1 ^ 2 * d2 = s ∧ Squarefree d2 := by
  obtain ⟨a, b, ha, hb, hab, hsf⟩ := Nat.sq_mul_squarefree_of_pos hspos
  -- `hab : b ^ 2 * a = s` with the square first; the wanted orientation is
  -- `d1 ^ 2 * d2 = s`, so `d1 := b` and `d2 := a` with no reordering needed.
  exact ⟨b, a, hb, ha, hab, hsf⟩

end SqFree
end OddPerfectNumber.Kernel

theorem solution (s : Nat) (hspos : 0 < s) :
    ∃ d1 d2 : Nat, 0 < d1 ∧ 0 < d2 ∧ d1 ^ 2 * d2 = s ∧ Squarefree d2 :=
  OddPerfectNumber.Kernel.SqFree.solution_aux s hspos
