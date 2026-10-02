-- Prove2me | solution 1 for OddPerfectNumber.Kernel.three_kernel_prime_when_p_one_mod_three
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T10:43:25.734852+00:00
-- url     : https://prove2.me/submissions/1381e130-ea8e-4616-bc04-5c1cfde37754

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- Target: OddPerfectNumber.Kernel.three_kernel_prime_when_p_one_mod_three
--          257119a0-ae2a-479f-9429-8954f48c02b5
--
-- REPAIRS FOR CANDIDATE 6295 (6 error groups, covering 3 distinct root causes).
--
-- ROOT CAUSE 1 -- `Nat.mod_modEq` orientation (E02).  `Nat.mod_modEq p 9 : p % 9 ≡ p [MOD 9]`
--   but the goal needs `p ≡ p % 9 [MOD 9]`; `Nat.ModEq` is an equation, so `.symm` is exact.
--
-- ROOT CAUSE 2 -- `Nat.ModEq.pow` exponent position (E03, E04).  It is declared
--   `pow (m : ℕ) (h : a ≡ b [MOD n])`, so the exponent is the FIRST explicit argument;
--   `hp9.pow 2` projects as `fun m => Nat.ModEq.pow m hp9` and is rejected by `Nat.ModEq.add`
--   for expecting a Prop, with the numeral `2` then landing in a Prop metavariable.
--   REPAIR: `hp9.pow 2`.
--
-- ROOT CAUSE 3 -- `interval_cases` parser (E01, E02, E03).  `using` takes TWO comma-separated
--   terms as a tactic suffix, so `interval_cases h : p % 9 using hres9` does not parse at all
--   ("unexpected token '<;>'; expected ','").  E02 is the parser's own follow-on complaint and
--   E03 is reported at line 38 simply because a parse failure makes the whole proof body
--   unavailable to the elaborator; all three groups are the one defect.  REPAIR: use the plain
--   form, which scans the context for bounds with `mustUseBounds := false` and therefore takes
--   both the automatic `Nat` lower bound and the in-context `hres9 : p % 9 < 9`.
--
-- E06 (L36, UNSOLVED GOALS) is the earliest reported line and the one that actually mattered.
--   `explain` shows this target carries an OPEN `unsolved-goals` cause seen 18 times, and a
--   sibling attempt (6287) reproduced it: the contradiction branch used the divisibility
--   witness `q * (9 * c^2)` for `9 ∣ q * x^2`.  From `3 ∣ x` we get `x = 3 * c`, so
--   `x^2 = 9 * c^2` and `q * x^2 = 9 * (q * c^2)` -- the witness is `q * c^2`, NOT
--   `q * (9 * c^2)`, which overshoots by a factor of nine and leaves `ring` unable to close the
--   goal.  That is precisely why 6287's four `ring` steps reported "unsolved goals".
--   REPAIR: the witness is `q * c^2` (resp. `r * c^2`), and the contradiction is closed by
--   rewriting forward with `hsplit`, whose LEFT-hand side is the occurrence in the goal.
import Mathlib

namespace OddPerfectNumber
namespace Kernel

theorem solution_holds (p m d1 q r x : Nat) (hp : p.Prime) (hp2 : p != 2) (hp4 : p % 4 = 1)
    (hm : Odd m) (hpm : ¬ p ∣ m) (hq : q.Prime) (hr : r.Prime) (hp3 : p % 3 = 1)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r)))
    (hsplit : p ^ 2 + p + 1 = q * x ^ 2 ∨ p ^ 2 + p + 1 = r * x ^ 2) :
    q = 3 ∨ r = 3 := by
  have h3pr : (3 : Nat).Prime := by norm_num
  have hpm3 : p ≡ (1 : Nat) [MOD 3] := hp3
  have hsum3 : p ^ 2 + p + 1 ≡ (1 + 1 + 1 : Nat) [MOD 3] :=
    Nat.ModEq.add (Nat.ModEq.add (hpm3.pow 2) hpm3) (Nat.ModEq.refl 1)
  have hmod3 : (p ^ 2 + p + 1) % 3 = 0 := by
    rwa [Nat.ModEq] at hsum3
  have h3 : (3 : Nat) ∣ p ^ 2 + p + 1 := Nat.dvd_of_mod_eq_zero hmod3
  have h9 : ¬ (9 : Nat) ∣ p ^ 2 + p + 1 := by
    intro hz9
    have hmod9 : (p ^ 2 + p + 1) % 9 = 0 :=
      (@Nat.dvd_iff_mod_eq_zero 9 (p ^ 2 + p + 1)).mp hz9
    have hp9 : p ≡ p % 9 [MOD 9] := (Nat.mod_modEq p 9).symm
    have hsum9 : p ^ 2 + p + 1 ≡ (p % 9) ^ 2 + p % 9 + 1 [MOD 9] :=
      Nat.ModEq.add (Nat.ModEq.add (hp9.pow 2) hp9) (Nat.ModEq.refl 1)
    rw [Nat.ModEq] at hsum9
    rw [hsum9] at hmod9
    have hres9 : p % 9 < 9 := Nat.mod_lt _ (by omega)
    interval_cases h : p % 9 <;> norm_num [Nat.not_lt_zero] at hmod9
  rcases hsplit with hsplit | hsplit
  · left
    have hdvd : (3 : Nat) ∣ q * x ^ 2 := by rw [← hsplit]; exact h3
    rcases h3pr.dvd_mul.mp hdvd with hq3 | hx23
    · exact (Nat.prime_dvd_prime_iff_eq h3pr hq).mp hq3 |>.symm
    · exfalso
      have hxx : (3 : Nat) ∣ x * x := by
        rw [show x * x = x ^ 2 from by ring]
        exact hx23
      rcases h3pr.dvd_mul.mp hxx with hx1 | hx2
      · obtain ⟨c, hc⟩ := hx1
        refine h9 ?_
        refine ⟨q * c ^ 2, ?_⟩
        rw [hsplit, hc]
        ring
      · obtain ⟨c, hc⟩ := hx2
        refine h9 ?_
        refine ⟨q * c ^ 2, ?_⟩
        rw [hsplit, hc]
        ring
  · right
    have hdvd : (3 : Nat) ∣ r * x ^ 2 := by rw [← hsplit]; exact h3
    rcases h3pr.dvd_mul.mp hdvd with hr3 | hx23
    · exact (Nat.prime_dvd_prime_iff_eq h3pr hr).mp hr3 |>.symm
    · exfalso
      have hxx : (3 : Nat) ∣ x * x := by
        rw [show x * x = x ^ 2 from by ring]
        exact hx23
      rcases h3pr.dvd_mul.mp hxx with hx1 | hx2
      · obtain ⟨c, hc⟩ := hx1
        refine h9 ?_
        refine ⟨r * c ^ 2, ?_⟩
        rw [hsplit, hc]
        ring
      · obtain ⟨c, hc⟩ := hx2
        refine h9 ?_
        refine ⟨r * c ^ 2, ?_⟩
        rw [hsplit, hc]
        ring

end Kernel
end OddPerfectNumber

open OddPerfectNumber.Kernel

theorem solution (p m d1 q r x : Nat) (hp : p.Prime) (hp2 : p != 2) (hp4 : p % 4 = 1)
    (hm : Odd m) (hpm : ¬ p ∣ m) (hq : q.Prime) (hr : r.Prime) (hp3 : p % 3 = 1)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r)))
    (hsplit : p ^ 2 + p + 1 = q * x ^ 2 ∨ p ^ 2 + p + 1 = r * x ^ 2) :
    q = 3 ∨ r = 3 :=
  OddPerfectNumber.Kernel.solution_holds p m d1 q r x hp hp2 hp4 hm hpm hq hr hp3 h1 hsplit
