-- Prove2me | solution 1 for ValuationSubring.exists_liesOverPrime_algebraicClosure_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b4096d24-db4c-5f89-a827-0e0e0df72678

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat

theorem solution (p : Nat.Primes) :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (p : ℕ) := by
  have hq : (p : ℕ).Prime := p.2

  set R : Subring (AlgebraicClosure ℚ) := ⊥ with hR

  have hqR : ¬IsUnit (((p : ℕ) : ℕ) : R) := by
    rw [isUnit_iff_exists_inv]
    rintro ⟨y, hy⟩
    have hy' : ((p : ℕ) : AlgebraicClosure ℚ) * (y : AlgebraicClosure ℚ) = 1 := by
      have := congrArg (R.subtype) hy
      simpa using this
    obtain ⟨n, hn⟩ := Subring.mem_bot.mp y.2
    rw [← hn] at hy'
    have hqn : ((p : ℕ) : ℤ) * n = 1 := by
      have : ((((p : ℕ) : ℤ) * n : ℤ) : AlgebraicClosure ℚ) = ((1 : ℤ) : AlgebraicClosure ℚ) := by
        push_cast
        linear_combination hy'
      exact_mod_cast this
    have h1 : ((p : ℕ) : ℤ) ≤ 1 := Int.le_of_dvd one_pos ⟨n, hqn.symm⟩
    have h2 : 2 ≤ (p : ℕ) := hq.two_le
    omega

  obtain ⟨B, -, hB⟩ :=
    Ideal.image_subset_nonunits_valuationSubring (Ideal.span {(((p : ℕ) : ℕ) : R)})
      (fun h => hqR (Ideal.span_singleton_eq_top.mp h))
  refine ⟨B, hB ⟨(((p : ℕ) : ℕ) : R), Ideal.subset_span rfl, ?_⟩⟩
  simp

end S_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
end P2MW
export P2MW.S_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat (solution)
