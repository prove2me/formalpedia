-- Prove2me | solution 1 for OddPerfectNumber.Kernel.isSq_iff_even_factorization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T11:43:37.668934+00:00
-- url     : https://prove2.me/submissions/25fe7c82-7093-4a53-b7e5-a9202da37e8b

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- Generic bridge between "is a square" and "every prime exponent is even".
--
-- Forward: `Nat.factorization_pow` rewrites `(y^2).factorization` to
-- `2 • y.factorization`, which is pointwise `j + j`, i.e. `Even`.
--
-- Reverse: `Nat.floorRoot 2 n` is *defined* to be the product of `p^(e_p/2)`
-- over the prime support, and `Nat.factorization_floorRoot` already proves
-- that its factorization is `n.factorization ⌊/⌋ 2`.  So it suffices to check
-- that this pointwise half equals the true integer half `e_p / 2` at every
-- prime, which is exactly `Even e_p`.
--
-- Design note (three dead ends, all remote CEs, all preserved here because the
-- failure modes are not obvious):
--   1. Unfolding the explicit `Finset` product by hand needs an additive
--      `Finset.sum_eq_single`; the pinned revision only has `prod_eq_single`.
--   2. `Finsupp.onFinset` over `n.primeFactors` fixes a `Decidable` instance for
--      its filter predicate, and the later `Finset.mem_filter` use picks a
--      *different* instance, giving an unfixable
--      "synthesized type class instance is not definitionally equal".
--   3. Hand-writing the halved Finsupp as `fun p => n.factorization p / 2`
--      is a plain `ℕ → ℕ`, not a `ℕ →₀ ℕ`; `Finsupp` has no pointwise `/`
--      (only `Finsupp.floorDiv`).  Use `Nat.floorRoot` instead.
import Mathlib

namespace OddPerfectNumber.Kernel
namespace Bridge

/-- An even natural number is twice its own half. -/
theorem two_mul_half_of_even {e : Nat} (he : Even e) : e = 2 * (e / 2) := by
  obtain ⟨j, hj⟩ := he
  have hcanc := (Nat.div_mul_cancel (show (2 : Nat) ∣ j + j from ⟨j, by ring⟩)).symm
  omega

theorem isSq_iff_even_factorization {n : Nat} (hn : n ≠ 0) :
    (∃ y, y ^ 2 = n) ↔ ∀ p : Nat, Even (n.factorization p) := by
  classical
  constructor
  · rintro ⟨y, rfl⟩ p
    rw [Nat.factorization_pow, Finsupp.nsmul_apply, Nat.nsmul_eq_mul, Nat.two_mul]
    exact ⟨_, rfl⟩
  · intro hall
    refine ⟨Nat.floorRoot 2 n, ?_⟩
    -- Identify `n` with `(Nat.floorRoot 2 n)^2` via unique factorization.
    refine Nat.eq_of_factorization_eq' (pow_ne_zero 2 (Nat.floorRoot_ne_zero.mpr ⟨by norm_num, hn⟩)) hn ?_
    rw [Nat.factorization_pow, Nat.factorization_floorRoot]
    -- Pointwise, doubling the halved exponent recovers it, since all are even.
    refine Finsupp.ext ?_
    intro p
    obtain ⟨j, hj⟩ := hall p
    rw [Finsupp.nsmul_apply, Finsupp.coe_floorDiv, smul_eq_mul]
    simp only [Nat.floorDiv_eq_div]
    rw [hj]
    omega

end Bridge
end OddPerfectNumber.Kernel

theorem solution {n : Nat} (hn : n ≠ 0) :
    (∃ y, y ^ 2 = n) ↔ ∀ p : Nat, Even (n.factorization p) :=
  OddPerfectNumber.Kernel.Bridge.isSq_iff_even_factorization hn
