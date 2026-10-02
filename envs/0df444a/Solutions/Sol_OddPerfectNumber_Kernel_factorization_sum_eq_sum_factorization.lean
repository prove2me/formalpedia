-- Prove2me | solution 1 for OddPerfectNumber.Kernel.factorization_sum_eq_sum_factorization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T21:09:29.618612+00:00
-- url     : https://prove2.me/submissions/b32f8653-221d-487c-a1ce-eea93430ea80

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
--
-- The p-adic multiplicity of the divisor sum of m squared is the SUM of the
-- p-adic multiplicities of its prime-power local factors.
--
-- This is the central finite-sum identity of the sigma-source toolkit.  It is what
-- turns "the total p-multiplicity of sigma(m^2) is 5" into a statement about the
-- INDIVIDUAL local factors, so an incoming sigma source of the Euler prime can be
-- located and its local p-valuation measured.
--
-- It rests on two Proved results:
--   * `Kernel.sum_divisors_eq_prod_prime_pow` (39086529): the divisor sum of `m ^ 2`
--     is the product of the divisor sums of its prime-power local factors;
--   * Mathlib's `Nat.factorization_prod_apply`, which distributes the multiplicity of
--     `p` across a finite product as a sum of multiplicities.
--
-- Every local factor is nonzero because `1` is a divisor of every positive prime
-- power, so the divisibility hypothesis of `Nat.factorization_prod_apply` holds; that
-- is the only side condition, and it is discharged pointwise below.
--
-- Target shape: it is stated generically so that it can be applied to `q`, `r` and
-- `p` alike.
import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_sum_divisors_eq_prod_prime_pow

namespace OddPerfectNumber.Kernel
namespace ValSum

theorem solution_aux {m p : Nat} (hm0 : m != 0) :
    (∑ d ∈ (m ^ 2).divisors, d).factorization p =
      ∑ t ∈ m.primeFactors,
        (∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d).factorization p := by
  have hm0' : m ≠ 0 := by simpa using hm0
  have hsq0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0'
  -- Sigma is a product of the local divisor sums.
  have hprod := OddPerfectNumber.Kernel.sum_divisors_eq_prod_prime_pow hm0
  -- Every LOCAL factor is nonzero: `1` divides `t ^ (2 * m.factorization t)`, so
  -- its divisor sum is at least `1`.  This is the side condition
  -- `Nat.factorization_prod_apply` needs.
  have hfac0 : ∀ t ∈ m.primeFactors,
      (∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d) ≠ 0 := by
    intro t ht
    -- Each local divisor sum is nonzero.  `Nat.mem_divisors` reads
    --
    --   Nat.mem_divisors {m : Nat} : n ∈ divisors m <-> n | m ∧ m != 0
    --
    -- so a membership needs BOTH a divisibility and the nonzero of the underlying
    -- number.  `1` divides every natural (`Nat.one_dvd`), and the prime power is
    -- nonzero because `t` is prime and hence nonzero.
    have htp : t.Prime := (Nat.mem_primeFactors.mp ht).1
    have hpow0 : t ^ (2 * m.factorization t) ≠ 0 := pow_ne_zero _ htp.ne_zero
    have hone : (1 : Nat) ∈ (t ^ (2 * m.factorization t)).divisors :=
      Nat.mem_divisors.mpr ⟨one_dvd _, hpow0⟩
    -- A finite sum of naturals containing the term `1` is positive.  The declaration
    -- is `Finset.sum_pos` (NOT `Finset.sum_pos'`, which is the `Finsupp` version and
    -- took three implicit arguments Lean could not synthesise -- candidate 5793
    -- reported `don't know how to synthesize implicit argument a_2 / a_1 / p`).
    -- Positivity of a finite sum of naturals containing the term `1`.
    --
    -- `Finset.sum_pos` is NOT the right declaration here: it is stated for a sum over
    -- `Finset.univ` of a `Fintype`-indexed family and expects
    -- `∀ i ∈ (...).divisors, 0 < i`, which candidate 5838 reported verbatim
    -- (`Supplied term: hexists / Actual type: Exists d in ..., 0 < d
    --  / Expected type: ∀ i in ..., 0 < i`).  Its sibling
    --
    --   Finset.sum_pos_iff_of_nonneg (h : ∀ i ∈ s, 0 ≤ f i) :
    --     0 < ∑ i ∈ s, f i ↔ Exists i ∈ s, 0 < f i
    --
    -- has exactly the shape needed (Mathlib
    -- `Algebra/Order/BigOperators/Group/Finset.lean:176`), so the nonnegativity of
    -- every summand discharges the hypothesis and the known member `1` discharges the
    -- existential.
    have hnonneg : ∀ d ∈ (t ^ (2 * m.factorization t)).divisors, (0 : Nat) ≤ d :=
      fun d _ => Nat.zero_le d
    have hpos : 0 < ∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d :=
      (Finset.sum_pos_iff_of_nonneg hnonneg).mpr ⟨1, hone, by norm_num⟩
    exact ne_of_gt hpos
  -- Distribute the multiplicity of `p` across the product.
  --
  -- NO extra pointwise projection is applied here.  `Nat.factorization_prod_apply`
  -- already concludes with the value AT the point `p`, i.e. it IS
  --
  --   (S.prod g).factorization p = S.sum (fun x => (g x).factorization p)
  --
  -- Candidate 5882 reported the doubled application: the goal state showed
  --
  --   ((∏ t ∈ m.primeFactors, ...).factorization p).factorization p
  --     = (∑ x ∈ m.primeFactors, ...).factorization p
  --
  -- i.e. `congrArg (fun n => n.factorization p)` had wrapped a `.factorization p`
  -- around a statement that already carried one, and the rewrite with `hprod` then
  -- had no `∑ d ∈ (m ^ 2).divisors, d` to match.
  --
  -- Adding `(p := p)` in the previous round fixed the metavariable, which is what
  -- exposed this doubled projection; the projection is now dropped entirely.
  -- The earlier `congrFun` attempt (candidate 5783) failed for a different reason: the
  -- `Eq` was being passed where a FUNCTION was expected, which is what happens when the
  -- declaration's own conclusion is already pointwise.
  have hdist := Nat.factorization_prod_apply (p := p) (S := m.primeFactors)
    (g := fun t : Nat => ∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d) hfac0
  -- `hprod` is oriented `sigma(m^2) = prod ...`, i.e. it puts the DIVISOR SUM on the
  -- LEFT, while `hdist` needs the PRODUCT on the left.  Candidate 5901 reported
  -- `Did not find an occurrence of the pattern ∑ d ∈ (m ^ 2).divisors, d` with the
  -- target `(∏ t ∈ m.primeFactors, ...).factorization p = ...`, i.e. `rw [hprod]`
  -- searched for the sum on the left where only the product occurs.  The rewrite is
  -- therefore REVERSED.
  -- Diagnosis of candidates 5901, 5915, 5919 and 5925.  `hdist` is the
  -- distributivity of `Nat.factorization` over a finite product, oriented with the
  -- PRODUCT on the left:
  --
  --   hdist : (∏ t ∈ m.primeFactors, ...).factorization p = ∑ x ∈ m.primeFactors, ...
  --
  -- and the GOAL wants the divisor sum on the left.  Now that the doubled
  -- projection is gone the goal is exactly
  --
  --   (∑ d ∈ (m ^ 2).divisors, d).factorization p = ∑ t ∈ m.primeFactors, ...
  --
  -- so `hprod`, which reads `∑ d ∈ (m ^ 2).divisors, d = ∏ t ∈ m.primeFactors, ...`,
  -- applies to the goal in its FORWARD direction.  Candidate 5901's failure came
  -- from the doubled projection, which put the product on the left of the goal;
  -- 5915 and 5919 then wrongly used the reverse direction (`← hprod`), and 5925
  -- reported precisely that: the pattern it could not find was
  -- `∏ t ∈ m.primeFactors, ...` inside a goal that still contained the divisor
  -- sum.  The rewrite therefore belongs on the GOAL, forwards.
  rw [hprod]
  exact hdist

end ValSum
end OddPerfectNumber.Kernel

open OddPerfectNumber.Kernel

theorem solution {m p : Nat} (hm0 : m != 0) :
    (∑ d ∈ (m ^ 2).divisors, d).factorization p =
      ∑ t ∈ m.primeFactors,
        (∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d).factorization p :=
  OddPerfectNumber.Kernel.ValSum.solution_aux hm0
