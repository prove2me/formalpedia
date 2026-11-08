-- Prove2me | solution 1 for SmolenskyAC.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:40:27.191568+00:00
-- url     : https://prove2.me/submissions/d75e4d9b-d286-4c3a-bddc-4948a78360ab

import Mathlib

theorem solution (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∃ (F : Type) (_ : Field F), CharP F p ∧ ∃ a : F, a ≠ 1 ∧ a ^ q = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : NeZero ((q : ℕ) : ZMod p) := ⟨by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)⟩
  refine ⟨CyclotomicField q (ZMod p), inferInstance,
    charP_of_injective_algebraMap (algebraMap (ZMod p) _).injective p, ?_⟩
  have hz := IsCyclotomicExtension.zeta_spec q (ZMod p) (CyclotomicField q (ZMod p))
  exact ⟨_, hz.ne_one hq.one_lt, hz.pow_eq_one⟩
