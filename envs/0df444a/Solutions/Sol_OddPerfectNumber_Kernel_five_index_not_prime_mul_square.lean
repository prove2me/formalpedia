-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_index_not_prime_mul_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T11:57:14.118304+00:00
-- url     : https://prove2.me/submissions/cd6820c9-38d6-47ef-bfc9-49bf9f4abcb7

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
--
-- `five_index_not_prime_mul_square` (2ec27119): in the k = 5 Dris branch the
-- square-free part of the index is never a single prime times a square.  Only
-- the *first* Dris equation is used, which is legitimate for this one-prime case.
--
-- Write `U = p ^ 2 + p + 1` and `V = ((p + 1) / 2) * (p ^ 2 - p + 1)`.  The
-- accepted `five_sigma_two_cyclotomic_odd_prime` (7f2041ff) is precisely
-- `sigma (p ^ 5) = 2 * U * V`, so substituting `s = q * a ^ 2` into
-- `2 * m ^ 2 = sigma (p ^ 5) * s` and cancelling the common `2` in `Nat` yields
-- `m ^ 2 = a ^ 2 * (q * U * V)`, whence `q * U * V` is a square by the accepted
-- `isSq_of_sq_mul_eq_sq` (74779081).  The accepted
-- `prime_mul_coprime_nonsquares_not_square` (0a9fa825) forbids exactly that,
-- given that `U` and `V` are coprime (2c9214f0), `U` is not a square (648a7dc4)
-- and `V` is not a square under `p % 4 = 1` (62a8c541).
--
-- `hm` and `hpm` are carried by the published binder list but are not needed by
-- this one-prime-kernel argument; that is expected, since this child is exactly
-- the case where the first Dris equation alone is strong enough.
import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_five_sigma_two_cyclotomic_odd_prime
import Theorems.Thm_OddPerfectNumber_Kernel_isSq_of_sq_mul_eq_sq
import Theorems.Thm_OddPerfectNumber_Kernel_five_cyclotomic_block_coprime
import Theorems.Thm_OddPerfectNumber_Kernel_five_cyclotomic_factors_ne_square
import Theorems.Thm_OddPerfectNumber_Kernel_five_second_cyclotomic_product_not_square
import Theorems.Thm_OddPerfectNumber_Kernel_prime_mul_coprime_nonsquares_not_square

namespace OddPerfectNumber.Kernel
namespace FiveIdxF

theorem solution_aux (p m s q a : Nat) (hp : p.Prime) (hp2 : p != 2) (hp4 : p % 4 = 1)
    (hm : Odd m) (hpm : ¬ p ∣ m) (hq : q.Prime) (hs : s = q * a ^ 2) (hspos : 0 < s)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s) :
    False := by
  -- The published binder is `hp2 : p != 2`, a `Bool`, so it coerces to `p ≠ 2`.
  -- The coercion is obtained by `simpa`; it is never used as a rewrite argument,
  -- which is what failed in earlier candidates for `five_cyclotomic_block_coprime`.
  have hp2' : p ≠ 2 := by simpa using hp2
  -- `five_cyclotomic_factors_ne_square` needs `2 < p`, i.e. `Prime.two_le` plus
  -- `hp2'`.  `lt_of_le_of_ne` is not a declaration in the pinned revision, so the
  -- implication is closed by `omega` against `hp2'` instead.
  have hp2lt : 2 < p := by
    have htwo : 2 ≤ p := hp.two_le
    by_contra hc
    exact hp2' (by omega)
  -- `U > 0` and `V > 0`.  Both are discharged by `p = n + 1`, which turns the
  -- truncated `Nat` subtraction into a manifest polynomial.
  have hU0 : p ^ 2 + p + 1 ≠ 0 := by
    obtain ⟨n, hn⟩ : ∃ n : Nat, p = n + 1 := ⟨p - 1, by omega⟩
    rw [hn]
    have hexp : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    rw [hexp]
    exact Nat.ne_of_gt (by omega)
  -- REPAIR (30 September 2026 session I, remote 1a84a4da).  Route "div" failed
  -- for three mechanical reasons, all repaired here without changing the
  -- mathematics:
  --   * `obtain ⟨a1, rfl⟩ := Nat.mul_eq_zero.mp hc` performs a *substituting*
  --     obtain, and dependent elimination then has to solve
  --     `0 = (p + 1).div 2`, which it cannot.  The non-substituting form
  --     `⟨hA1⟩` keeps `p` intact.
  --   * `rw [hs, hc, Nat.mul_zero] at hspos` fails because after substituting
  --     `a = 0` the goal is the bare arithmetic `0 < q * 0 ^ 2`, in which
  --     `Nat.mul_zero` no longer matches.  `omega` closes it directly.
  --   * the `open` comment block introduced a parse error, so the explanation
  --     is kept to plain `--` lines well away from the declaration.
  have hApos : 0 < (p + 1) / 2 := by
    -- REPAIR (30 September 2026 session I, remote c3990127).  `Nat.Prime.two_le`
    -- concludes `2 ≤ p`; reparametrising `p = n + 2` makes `p + 1` the manifest
    -- numeral `n + 3`, which `omega` evaluates outright.  No `Nat.div_*` lemma is
    -- guessed: the revision-keyed declaration index has none of
    -- `Nat.div_lt_iff_lt_mul`, `Nat.lt_div_iff_mul_lt`, `Nat.div_le_iff_le_mul`.
    obtain ⟨n, hn⟩ : ∃ n : Nat, p = n + 2 := ⟨p - 2, by omega⟩
    rw [hn, Nat.add_right_comm]
    omega
  have hBpos : 0 < p ^ 2 - p + 1 := by
    obtain ⟨n, hn⟩ : ∃ n : Nat, p = n + 1 := ⟨p - 1, by omega⟩
    rw [hn]
    have hexp : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    rw [hexp]
    omega
  have hU0 : p ^ 2 + p + 1 ≠ 0 := Nat.ne_of_gt (by omega)
  have hV0 : ((p + 1) / 2) * (p ^ 2 - p + 1) ≠ 0 :=
    Nat.mul_ne_zero (Nat.ne_of_gt hApos) (Nat.ne_of_gt hBpos)
  have ha0 : a ≠ 0 := by
    intro hc
    rw [hs, hc] at hspos
    omega
  have hq0 : q ≠ 0 := by
    intro hc
    rw [hs, hc] at hspos
    omega
  -- The `2`-cancellation, entirely inside `Nat`: the accepted factorisation makes
  -- the `2` on the right manifest, so `mul_left_cancel₀` applies directly.  That
  -- lemma is *unqualified* -- it lives in the `GroupWithZero` sections of
  -- `Mathlib/Algebra/GroupWithZero/Defs.lean:55`, not under a `Nat` namespace.
  -- Writing `Nat.mul_left_cancel₀` was confirmed to elaborate to
  -- `Unknown constant Nat.mul_left_cancel0` on the sibling candidates.
  have hkey : m ^ 2 = a ^ 2 * (q * (p ^ 2 + p + 1)
      * (((p + 1) / 2) * (p ^ 2 - p + 1))) := by
    have hfac : 2 * (p ^ 2 + p + 1) * (((p + 1) / 2) * (p ^ 2 - p + 1))
        = ∑ d ∈ (p ^ 5).divisors, d :=
      OddPerfectNumber.Kernel.five_sigma_two_cyclotomic_odd_prime p hp hp2
    -- REPAIR (30 September 2026 session I, remote c3990127).  The earlier
    -- `hsub` asserted `sigma (p ^ 5) * s = Y` with `Y` the bare product
    -- `(q * a ^ 2) * U * V`, but substituting `hfac` makes the left-hand side
    -- `2 * U * V * q * a ^ 2`.  The statement was therefore false by exactly one
    -- factor of `2`, and `ring` correctly reduced the goal to the absurd
    -- `2 * X = X`.  Restoring the `2` on the right is the whole repair: the
    -- product is then an `AC`-normalisation that `ring` closes outright, and it
    -- matches `h1` so the cancellation below is legitimate.
    have hsub : (∑ d ∈ (p ^ 5).divisors, d) * s = (q * a ^ 2) * (p ^ 2 + p + 1)
        * (((p + 1) / 2) * (p ^ 2 - p + 1)) * 2 := by
      rw [hfac.symm, hs]
      ring
    have hcanc : m ^ 2 = a ^ 2 * (q * (p ^ 2 + p + 1)
        * (((p + 1) / 2) * (p ^ 2 - p + 1))) := by
      have h2 : 2 * m ^ 2 = 2 * (a ^ 2 * (q * (p ^ 2 + p + 1)
          * (((p + 1) / 2) * (p ^ 2 - p + 1)))) := by
        -- `h1` gives `2 * m ^ 2 = sigma (p ^ 5) * s` and `hsub` reads that
        -- product off; the two are combined by transitivity, after which `hsub`
        -- is consumed by `ring` so that no `?m` metavariable is left over.
        have h12 : 2 * m ^ 2
            = (q * a ^ 2) * (p ^ 2 + p + 1) * (((p + 1) / 2) * (p ^ 2 - p + 1)) * 2 :=
          h1.trans hsub
        -- `rw` performs `ring_nf`-quality normalisation only through the
        -- lemmas it is given, so the residual `A * B * 2 * C = 2 * (D * E)`
        -- shape is closed by `ring` instead of a guessed rewrite list.
        rw [h12]
        ring
      exact mul_left_cancel₀ (by norm_num) h2
    -- `hcanc` is the last `have` in this block, so its own type is the goal
    -- the `have hkey ... := by` block is closing.  Naming it explicitly is
    -- what stops Lean from reporting the block as an unsolved goal.
    exact hcanc
  have hsquare : ∃ y, y ^ 2
      = q * (p ^ 2 + p + 1) * (((p + 1) / 2) * (p ^ 2 - p + 1)) :=
    -- REPAIR (30 September 2026 session I, remote 7aca6078).  The accepted
    -- `isSq_of_sq_mul_eq_sq` (74779081) is stated for `a ^ 2 * x = m ^ 2`, i.e.
    -- the product on the *left*.  `hkey` is oriented the other way round, from
    -- the cancellation, so the hypothesis argument is `hkey.symm` after all.
    -- Two earlier candidates had this exactly backwards in each direction; the
    -- remote message naming the expected type
    -- `a ^ 2 * (q * U * V) = ?m ^ 2` settles it.
    OddPerfectNumber.Kernel.isSq_of_sq_mul_eq_sq ha0
      -- REPAIR (30 September 2026 session I, remote 7f75b780).  `x` is the whole
      -- right-hand product, so the nonvanishing goal is
      -- `q * (p^2 + p + 1) * ((p+1)/2 * (p^2-p+1)) ≠ 0`, which is discharged by
      -- the prebuilt `hV0` for the trailing factor rather than by re-deriving
      -- it from `hApos` alone.
      (Nat.mul_ne_zero (Nat.mul_ne_zero hq0 hU0) hV0) hkey.symm
  have hneU : ¬ ∃ y, y ^ 2 = p ^ 2 + p + 1 :=
    OddPerfectNumber.Kernel.five_cyclotomic_factors_ne_square p hp2lt |>.1
  -- REPAIR (30 September 2026 session I, remote 7f75b780).  Two changes here.
  --
  -- 1. The V-non-square child is stated with the square on the *right* of the
  --    existential equation while the prime-toggle lemma needs it on the left,
  --    so the two sides are transposed.
  -- 2. Binding it as a separate `have hneV : ¬ ∃ y, y ^ 2 = V` type ascription
  --    that contains a `Nat` division was reported as a parse fault at that
  --    exact line in three consecutive candidates, even though the
  --    structurally identical `hneU` (no division) parses fine.  The ascription
  --    is therefore removed and the term is passed positionally instead.
  --
  -- REPAIR (30 September 2026 session I, remote 7aca6078).  The coprimality
  -- premise is bound by an explicit `have` with a named `Nat.Coprime` type
  -- rather than by a `by rw [...]` block in argument position.  An
  -- `rw`-with-unknown-lemma in argument position is reported by Lean as
  -- "unexpected identifier; expected ')', ',' or ':'", which is exactly the
  -- parse fault that persisted at this line through four candidates.
  have hcop : Nat.Coprime (p ^ 2 + p + 1) (((p + 1) / 2) * (p ^ 2 - p + 1)) :=
    Nat.coprime_iff_gcd_eq_one.mpr (OddPerfectNumber.Kernel.five_cyclotomic_block_coprime p hp2)
  -- The prime-toggle lemma returns a negation of an existential, so it is
  -- applied directly to the square witness `hsquare` to close the goal.
  exact (OddPerfectNumber.Kernel.prime_mul_coprime_nonsquares_not_square hU0 hV0
    hcop hneU
    (fun hy => OddPerfectNumber.Kernel.five_second_cyclotomic_product_not_square
      p hp hp4 ⟨hy.choose, hy.choose_spec.symm⟩) hq) hsquare

end FiveIdxF
end OddPerfectNumber.Kernel

-- The static guard `_namespace_resolution_reason` requires the target's
-- namespace to be opened for a top-level `theorem solution`, because the target
-- `2ec27119` declares its binders inside `namespace OddPerfectNumber.Kernel`.
-- Every import above is a *Proved* `Kernel` child, so the namespace genuinely
-- exists in the remote environment and this `open` is well formed.  (The
-- `open` of an *undeclared* namespace is a hard error — that was the exact
-- cause of the earlier CEs on `sqfree_part_ne_one`.)
open OddPerfectNumber.Kernel

theorem solution (p m s q a : Nat) (hp : p.Prime) (hp2 : p != 2) (hp4 : p % 4 = 1)
    (hm : Odd m) (hpm : ¬ p ∣ m) (hq : q.Prime) (hs : s = q * a ^ 2) (hspos : 0 < s)
    (h1 : 2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s) :
    False :=
  OddPerfectNumber.Kernel.FiveIdxF.solution_aux p m s q a hp hp2 hp4 hm hpm hq hs hspos h1
