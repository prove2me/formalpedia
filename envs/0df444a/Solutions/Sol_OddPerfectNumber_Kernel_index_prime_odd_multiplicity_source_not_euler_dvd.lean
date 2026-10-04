-- Prove2me | solution 1 for OddPerfectNumber.Kernel.index_prime_odd_multiplicity_source_not_euler_dvd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-03T10:32:16.919986+00:00
-- url     : https://prove2.me/submissions/392aedcb-1a91-48b3-a27e-60c549299c99

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- Target: OddPerfectNumber.Kernel.index_prime_odd_multiplicity_source_not_euler_dvd
--          9a610274-5ae3-4e0f-b518-a3bf4190c1be
--
-- `index_prime_has_odd_multiplicity_source` (48e8fb88) is Proved, but it carries the
-- hypothesis `p | m`.  In the hard residual `6eb10265` we have `Not (p | m)`, so that
-- statement cannot be instantiated: the hypothesis it needs is exactly the false one.
--
-- INSPECTING THE ACCEPTED PROOF OF 48e8fb88 (candidate 6612, submission ea6d310e,
-- source 7c91c35c) SHOWS `hpm` IS NEVER USED.  The whole proof reads only `hpow`,
-- `hn6` and `hm2`: the budget `v_p(sigma(m^2)) = 5` comes from `factorization_le_iff_dvd`
-- in the `.mpr` direction, the sum over the prime support comes from
-- `sum_divisors_eq_prod_prime_pow` plus `Nat.factorization_prod_apply`, and the odd
-- summand is extracted by a `Finset.induction_on` parity argument.  `hpm` is a dead
-- binder.
--
-- THIS FILE IS THEREFORE THE ACCEPTED SOURCE WITH THE DEAD BINDER REMOVED, which is the
-- corrected statement, and it is re-verified from scratch against this target.  Every
-- non-obvious step is annotated below with the API it uses and why the direction of
-- the rewrite or conversion is the one taken.
import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_sum_divisors_eq_prod_prime_pow

open OddPerfectNumber
open OddPerfectNumber.Kernel

theorem solution {m p : Nat} (hp : p.Prime) (hm2 : m ^ 2 != 0)
    (hpow : Dvd.dvd (p ^ 5) (∑ x ∈ (m ^ 2).divisors, x))
    (hn6 : Not (Dvd.dvd (p ^ 6) (∑ x ∈ (m ^ 2).divisors, x))) :
    exists t : Nat, Dvd.dvd t m /\ Dvd.dvd p (∑ i ∈ Finset.range ((m ^ 2).factorization t + 1), t ^ i) /\
      Not (Even ((∑ i ∈ Finset.range ((m ^ 2).factorization t + 1), t ^ i).factorization p)) := by
  classical
  -- E01: `hm2` is `(m ^ 2 != 0) = true`, i.e. a BOOLEAN `bne`.  `bne_iff_ne` is the bridge that the
  -- `decide`-free form needs; `simp at hm2` alone leaves the goal open.
  have hm2' : m ^ 2 ≠ 0 := by simpa only [bne_iff_ne] using hm2
  have hm0 : m ≠ 0 := fun hz => hm2' (by simp [hz])
  have hm0b : m != 0 := by simpa only [bne_iff_ne] using hm0
  -- E02: strict positivity of a prime power whose exponent may be `0`.  `t ^ 0 = 1`, so positivity
  -- holds unconditionally; `positivity` cannot derive it, so it is split out explicitly.
  have hloc : ∀ t ∈ m.primeFactors,
      (∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d) ≠ 0 := by
    intro t ht
    have htp : t.Prime := (Nat.mem_primeFactors.mp ht).1
    -- E01 of candidate 6556: `Nat.one_le_pow` expects `0 < m`, and `Nat.succ_le_succ htpos` produced
    -- `(Nat.succ 0).succ <= t.succ` instead, so that route is abandoned.  Primality gives `2 <= t`
    -- and `pow_pos (h) n` is the direct positivity lemma, in exactly the form already accepted in
    -- this corpus (03_SquareCancellation.lean:26).  `Nat.pow_pos` (dotted) does NOT resolve here.
    have htwo : 2 ≤ t := htp.two_le
    have htpos : 0 < t := htp.pos
    have hpos : 0 < t ^ (2 * m.factorization t) := by
      exact pow_pos htpos _
    rw [← ArithmeticFunction.sigma_one_apply]
    exact ne_of_gt (ArithmeticFunction.sigma_pos 1 _ (ne_of_gt hpos))
  -- E03: the dividend is nonzero because `p ^ 6` does not divide it while `p ^ 5` does; the
  -- contradiction is read off `0 | n` rather than by `subst`-ing a compound equality.
  have hneS : (∑ x ∈ (m ^ 2).divisors, x) ≠ 0 := by
    -- E01 of candidate 6593 (the last error group): every earlier version of this step tried to
    -- contradict `p ^ 5 | 0`, and the report "`simp` made no progress" is the tip of a MATHEMATICAL
    -- dead end rather than a syntactic one -- in `Nat` every number divides `0`, so `5 | 0` is TRUE
    -- and no fact about the divisor can be recovered from that equation.
    --
    -- The correct reason the dividend is nonzero is its SHAPE, not the divisibility hypothesis: the
    -- divisor sum of any `n` contains the divisor `1`, so it is at least `1`.  `Nat.one_mem_divisors`
    -- supplies the membership, so `hneS` holds for EVERY `m` and needs none of `hpow`, `hn6` or the
    -- zero-product route at all.
    --
    -- Positivity is obtained by comparing the sum against the SINGLETON `{1}`: the summand function is
    -- nonnegative everywhere, so `Finset.sum_le_sum_of_subset` (Finset.lean:424, the `to_additive` of
    -- `prod_le_prod_of_subset'`, which needs only canonical ordering -- satisfied by `Nat`) gives
    -- `sum over {1} <= sum over divisors`, i.e. `1 <= sum`.
    --
    -- E01/E02 of candidate 6608: the previous version used `Finset.univ.filter (fun x => x = 1)` to
    -- stand for the singleton, and `Finset.univ` needs a `Fintype` instance.  `Nat` HAS NO `Fintype`
    -- instance, so Lean reported "failed to synthesize instance of type class `Fintype Nat`" twice,
    -- at the `hne` line and again at the `hle` line.  `Finset.singleton 1` is the correct finite set
    -- and needs no instance at all.
    --
    -- E03 of candidate 6608 (`Unknown identifier hne`) and E04 (the comparison produced
    -- `sum over {x | x = 1} <= sum`, a FILTER sum rather than the literal `1`, so the closing `omega`
    -- could not see it) are both consequences of that same `univ` mistake: with the filter the
    -- subset proof failed, so `hne` was never introduced.  Replacing it by `singleton` fixes all four
    -- groups at once, and the comparison now genuinely has `1` on its left-hand side.
    --
    -- Names deliberately NOT used because they do not exist in this revision:
    -- `Finset.sum_pos'` and `Finset.single_le_sum` (only `Finsupp` analogues at
    -- Data/Finsupp/Order.lean:67 and :112), and `sum_le_sum_of_subset_of_nonneg`, whose name appears
    -- at Finset.lean:131 only as the `to_additive` TAG of a multiplicative lemma.
    intro hz
    -- `Nat.one_mem_divisors : 1 ∈ divisors n <-> n != 0` (NumberTheory/Divisors.lean:117), so the
    -- membership follows from `hm2'` by `.mpr`.
    have hone : (1 : Nat) ∈ (m ^ 2).divisors := Nat.one_mem_divisors.mpr hm2'
    have hne : ({1} : Finset Nat) ⊆ (m ^ 2).divisors := by
      intro x hx
      simpa only [Finset.mem_singleton.mp hx] using hone
    have hle : (1 : Nat) ≤ ∑ x ∈ (m ^ 2).divisors, x := by
      have h := Finset.sum_le_sum_of_subset
        (s := ({1} : Finset Nat))
        (t := (m ^ 2).divisors) (f := fun x : Nat => x) hne
      simpa using h
    exact absurd (by simpa using hz) (by omega)
  -- E04/E05/E07 (THE ROOT CAUSE).  `factorization_le_iff_dvd` reads
  --     d.factorization <= n.factorization  <->  d | n
  -- so the DIVISIBILITY hypothesis must be turned into a FINSUPP INEQUALITY with `.mpr`, and the
  -- inequality is then turned back into a bound at the prime with `.mp` plus `factorization_pow_self`.
  -- Both budgets are therefore established with a single `.mpr` each, and `hpow_self` reads the value.
  have hge : 5 ≤ (∑ x ∈ (m ^ 2).divisors, x).factorization p := by
    have h := (Nat.factorization_le_iff_dvd (pow_ne_zero 5 hp.ne_zero) hneS).mpr hpow
    -- E03 of candidate 6556: `rwa [Nat.factorization_pow_self hp]` FAILED with "Did not find an
    -- occurrence of the pattern `(p ^ ?m).factorization p` in `(p ^ 5).factorization <= S.factorization`
    -- -- the target of the rewrite is the whole order relation, and `factorization_pow_self` is
    -- about evaluating a FINSUPP at `p`, which is not what is syntactically present.  The correct move
    -- is to read the order relation POINTWISE with `Finsupp.single_le_iff`, whose statement is
    -- `single i x <= f <-> x <= f i` (Finsupp/Order.lean:207), after turning the left side into
    -- `single p 5` with `hp.factorization_pow` (Defs.lean:204).  No rewriting of `h` is needed.
    exact Finsupp.single_le_iff.mp (by simpa [hp.factorization_pow] using h)
  have hlt : (∑ x ∈ (m ^ 2).divisors, x).factorization p < 6 := by
    by_contra hcon
    have h6 : 6 ≤ (∑ x ∈ (m ^ 2).divisors, x).factorization p := by omega
    -- `6 <= s p` is POINTWISE `single p 6 <= s.factorization` by `Finsupp.single_le_iff`
    -- (Finsupp/Order.lean:207), and `(p ^ 6).factorization = single p 6` is `hp.factorization_pow`.
    -- No named-argument use of `Finsupp.single` appears here: that was E06.
    have hle : (p ^ 6).factorization ≤ (∑ x ∈ (m ^ 2).divisors, x).factorization := by
      rw [hp.factorization_pow]
      exact Finsupp.single_le_iff.mpr h6
    exact absurd (hn6 ((Nat.factorization_le_iff_dvd (pow_ne_zero 6 hp.ne_zero) hneS).mp hle))
      (by simp)
  have hval : (∑ x ∈ (m ^ 2).divisors, x).factorization p = 5 := by omega
  -- The valuation of the product is the sum of the local valuations.  `Nat.factorization_prod_apply`
  -- states the right-hand side as `S.sum (fun x => ...)`, which is the iterated `sum` notation.
  have hsum : (∑ x ∈ (m ^ 2).divisors, x).factorization p
      = ∑ t ∈ m.primeFactors, (∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d).factorization p := by
    rw [sum_divisors_eq_prod_prime_pow hm0b, Nat.factorization_prod_apply hloc]
  -- A finite sum of even numbers is even.
  have hevensum : ∀ U : Finset Nat,
      (∀ t ∈ U, Even ((∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d).factorization p)) →
      Even (∑ t ∈ U, (∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d).factorization p) := by
    intro U hU
    induction U using Finset.induction_on with
    | empty => simp
    | @insert t U ht ih =>
        rw [Finset.sum_insert ht]
        exact Even.add (hU t (Finset.mem_insert_self t U))
          (ih (fun u hu => hU u (Finset.mem_insert_of_mem hu)))
  -- The total is 5, which is odd, so some member is odd.
  have hodd : ¬ Even (∑ t ∈ m.primeFactors,
      (∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d).factorization p) := by
    rw [← hsum, hval]
    -- E04 of candidate 6556: `absurd rfl (by decide)` reported "Expected type must not contain
    -- metavariables" for the goal `Not (5 = 5)`, because `by decide` had no ground type to decide
    -- and `rfl` fixed the wrong side.  `Even 5` is `exists k, 5 = 2 * k`, and no such `k` exists, so
    -- the contradiction is a one-line `omega` after DESTRUCTURING the `Even` witness.
    intro h5
    obtain ⟨k, hk⟩ := h5
    omega
  have hmember : ∃ t ∈ m.primeFactors,
      ¬ Even ((∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d).factorization p) := by
    by_contra hcon
    push_neg at hcon
    exact hodd (hevensum m.primeFactors hcon)
  obtain ⟨t, ht, htodd⟩ := hmember
  obtain ⟨htp, htdvd, htne⟩ := Nat.mem_primeFactors.mp ht
  -- E05/E06: BOTH arguments of `lt_or_ge` must be naturals.  Candidate 6556 still applied it to the
  -- FINSUPP (`... .factorization`, type `Nat ->0 Nat`) and reported "expected `Nat`, supplied
  -- `Nat ->0 Nat`", with E06 (`x : ?m is not an inductive datatype`) as its labelled cascade.  The
  -- value at `p` is written explicitly: `... .factorization p`.  An odd natural is nonzero, hence
  -- positive, hence `p` divides the local factor.
  have hvpos : 0 < (∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d).factorization p := by
    -- E02/E03 of candidate 6568: `Nat.zero_lt_of_lt h` failed with "expected `?m < X`, supplied
    -- `X < 1`", i.e. that lemma reads a hypothesis of the form `0 < ?m < X`, not `X < 1`, and the
    -- `cases` on the resulting `Even` witness then hit a dependent-elimination error inside
    -- `padicValNat`.  Neither helper is needed: `Even n` is `exists k, n = 2 * k`, and an odd `n`
    -- cannot have that form, so `omega` closes both branches directly on the VALVE.
    by_contra hz
    rcases Nat.lt_or_ge ((∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d).factorization p) 1
      with h | h
    · -- `v < 1` forces `v = 0`, and `0` is even -- contradicting `htodd`.
      -- E02 of candidate 6579: writing the contradiction as `obtain ⟨k, hk⟩ := h; omega` made `omega`
      -- run `cases` on the `Even`/`padicValNat` goal and fail dependent elimination on
      -- `padicValNat p (...)`.  The witness for `Even` is therefore never destructed; instead the
      -- value is shown to be literally `0` by `omega` alone, and `Nat.zero_even` closes `htodd`.
      have hv : (∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d).factorization p = 0 := by omega
      rw [hv] at htodd
      exact absurd htodd (by simp)
    · -- `1 <= v` contradicts `v = 0`.
      omega
  have hpdvd : p ∣ ∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d :=
    Nat.dvd_of_factorization_pos (by omega)
  -- E12/E13: the goal's local factor is ALREADY the `range (k+1)` geometric sum and its index is
  -- ALREADY `(m ^ 2).factorization t`, so the rewrite must go into the HYPOTHESES.  `hpow'` relates
  -- the two exponents, and rewriting with it inside `hpdvd`/`htodd` produces exactly the goal's
-- index.  `Nat.sum_divisors_prime_pow htp` then converts the divisor sum into the geometric sum.
  --
  -- E04/E05 of candidate 6568 corrected the DIRECTION of this step.  The previous version wrote
  -- `have hdvd' : ... := by rw [<- hpow']; exact hpdvd`, i.e. it rewrote `2 * m.factorization t`
  -- INTO the goal using `hpow'`.  `rw [<- hpow']` rewrites with the RIGHT-HAND SIDE `2 * ...`, and
  -- the goal `p | sum d in (t ^ ((m ^ 2).factorization t)).divisors, d` has `(m ^ 2).factorization t`,
  -- not `2 * m.factorization t`, so no occurrence exists: "Did not find an occurrence of the pattern
  -- `2 * m.factorization t`".  The evidence also shows `hdvd'` DID elaborate, which confirms the
  -- goal is reachable.  The correct direction is `rw [hpow']`, which replaces
  -- `(m ^ 2).factorization t` by `2 * m.factorization t` and lands exactly on `hpdvd`/`htodd`.
  have hpow' : (m ^ 2).factorization t = 2 * m.factorization t := by
    simp [Nat.factorization_pow]
  have hdvd' : p ∣ ∑ d ∈ (t ^ ((m ^ 2).factorization t)).divisors, d := by
    rw [hpow']
    exact hpdvd
  have hodd' : ¬ Even ((∑ d ∈ (t ^ ((m ^ 2).factorization t)).divisors, d).factorization p) := by
    rw [hpow']
    exact htodd
  refine ⟨t, htdvd, ?_, ?_⟩
  · -- E09/E10 of candidate 6556: `rw [Nat.sum_divisors_prime_pow htp]` reported "Did not find an
    -- occurrence of the pattern `sum x in (t ^ ?m).divisors, ?m x`" in the target `p | sum i in
    -- Finset.range ((m ^ 2).factorization t + 1), t ^ i`.  That is CORRECT BEHAVIOUR, not a defect:
    -- `Nat.sum_divisors_prime_pow` is `@[to_additive (attr := simp)]` and rewrites TOWARD the
    -- `range (k+1)` shape, which the goal ALREADY has.  So the lemma cannot fire on the goal at all,
    -- and the goal is discharged by rewriting the HYPOTHESIS the other way instead.  `hdvd'` is about
    -- the divisor sum at exponent `(m ^ 2).factorization t`, exactly matching the goal's index, so
    -- `simpa only [Nat.sum_divisors_prime_pow htp] using hdvd'` closes the goal directly.
    simpa only [Nat.sum_divisors_prime_pow htp] using hdvd'
  · -- As above, for the parity conjunct.
    simpa only [Nat.sum_divisors_prime_pow htp] using hodd'
