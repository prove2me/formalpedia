-- Prove2me | solution 1 for RobersonCx.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:41:56.75917+00:00
-- url     : https://prove2.me/submissions/2ba11bab-a7c4-4758-9ce4-a0a7af585170

import Mathlib

set_option autoImplicit false
namespace RobersonCx

theorem lemma_10 (r : ℕ) (hr : 2 ≤ r)
    (ha : ∃ a : ℤ, Int.gcd a r = 1 ∧ (a : ZMod r) ≠ 1 ∧ (a : ZMod r) ≠ -1) :
    {p : ℕ | p.Prime ∧ Nat.Coprime p r ∧ (p : ZMod r) ≠ 1 ∧ (p : ZMod r) ≠ -1}.Infinite := by
  obtain ⟨a, hgcd, h1, h2⟩ := ha
  haveI : NeZero r := ⟨by omega⟩
  have hu : IsUnit (a : ZMod r) := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime]
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]; exact hgcd
  have hinf := Nat.infinite_setOfPred_prime_and_eq_mod hu
  apply hinf.mono
  rintro p ⟨hp, hpa⟩
  refine ⟨hp, ?_, by rw [hpa]; exact h1, by rw [hpa]; exact h2⟩
  have : IsUnit (p : ZMod r) := by rw [hpa]; exact hu
  exact (ZMod.isUnit_iff_coprime p r).mp this

end RobersonCx

theorem solution (r : ℕ) (hr : 2 ≤ r)
    (ha : ∃ a : ℤ, Int.gcd a r = 1 ∧ (a : ZMod r) ≠ 1 ∧ (a : ZMod r) ≠ -1) :
    {p : ℕ | p.Prime ∧ Nat.Coprime p r ∧ (p : ZMod r) ≠ 1 ∧ (p : ZMod r) ≠ -1}.Infinite :=
  RobersonCx.lemma_10 r hr ha
