-- Prove2me | solution 1 for OPG37364.exists_lps13_prime_above
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T13:28:45.741365+00:00
-- url     : https://prove2.me/submissions/06def1c8-1ea7-49df-8968-077c483171ad

import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.NormNum.LegendreSymbol

set_option autoImplicit false


/-- Arbitrarily large primes satisfying the fixed-13 arithmetic conditions.
The explicit prime witness supplies Mathlib's Legendre-symbol instance. -/
theorem solution (B : ℕ) :
    ∃ (q : ℕ) (hq : q.Prime),
      max B 13 < q ∧ q ≡ 5 [MOD 52] ∧ q ≡ 1 [MOD 4] ∧
      @legendreSym q ⟨hq⟩ 13 = -1 := by
  obtain ⟨q, hqB, hq, hq52⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max B 13)
      (q := 52) (a := 5) (by norm_num) (by norm_num)
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  have hq13 : 13 < q := lt_of_le_of_lt (le_max_right B 13) hqB
  have hmod13 : q ≡ 5 [MOD 13] := hq52.of_dvd (by norm_num)
  have hmod4 : q ≡ 1 [MOD 4] := by
    have h := hq52.of_dvd (show 4 ∣ 52 by norm_num)
    simpa only [Nat.ModEq, Nat.reduceMod] using h
  have hmod13int : (q : ℤ) % 13 = 5 := by
    have h : q % 13 = 5 := hmod13
    exact_mod_cast h
  have hreverse : legendreSym 13 q = -1 := by
    rw [legendreSym.mod 13 (q : ℤ)]
    change legendreSym 13 ((q : ℤ) % 13) = -1
    rw [hmod13int]
    norm_num
  have hrecip : legendreSym q 13 = legendreSym 13 q :=
    legendreSym.quadratic_reciprocity_one_mod_four (p := 13) (q := q)
      (by norm_num) (by omega)
  exact ⟨q, hq, hqB, hq52, hmod4, hrecip.trans hreverse⟩
