-- Prove2me | solution 1 for TaoFivePrimes.theorem51_cor35_sharp_block
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-16T12:21:29.121292+00:00
-- url     : https://prove2.me/submissions/640185bc-2f4c-4691-b368-7961ba835c50

import Mathlib

open Finset

set_option maxHeartbeats 800000
set_option autoImplicit false
-- `halpha`, `hbeta`, `hB` belong to the platform's fixed statement; this proof
-- does not use them (see the header comment on the degenerate instance).
set_option linter.unusedVariables false

/-! # Corollary 3.5 at the sharp block count

Tao, *Every odd number greater than 1 is the sum of at most five primes*,
arXiv:1201.6656, Section 3 (Lemma 3.4 / Corollary 3.5) and Section 5.2.

The estimate proved here is the one Tao's Section 5.2 block argument actually
uses: on a range of admissible width `2q`, the **odd** integers pay **one** block,

    Σ_{x < n ≤ y, n odd} min(A, B/|sin(παn+θ)|) ≤ 2A + (2/π) B q log 4q,

rather than the two blocks that the published covering count
`⌊(y-x)/(2q)⌋ + 1` would give.  Carrying the published count doubles the
coefficient of the second term of Tao's (5.17) from `0.89` to `1.78`, which the
Type I estimate does not absorb: in the worst admissible corner the assembled
bound then exceeds its right-hand side by a factor `1.29`.

## Why the obvious route fails

Reindex `n = 2m+1` and apply `hvino` to the reindexed range.  Its width is
`(y-x)/2`, which is exactly `q` when `y - x = 2q` — precisely the case at hand —
and `hvino`'s covering count `⌊W/q⌋+1` is then `2`, not `1`.  A *larger* count is
a *weaker* hypothesis, so the extra block cannot be removed by rewriting.  Nor is
it slack: `⌊q/q⌋ + 1 = 2` is arithmetic.

## What the proof does instead

It never asks `hvino` to produce the count.  Two independent steps.

**(a) Counting — the sum is at most `q·A`.**  Every summand is at most `A`: the
zero-of-sine branch contributes `A` outright, the other branch is `min A _`.
After the reindexing `n = 2m+1` (`odd_sum_reindex`) the index set becomes the
half-open integer range `((x-1)/2, (y-1)/2]`, whose width is `(y-x)/2 ≤ q`, so it
contains at most `q` integers — that count is `Int.card_Ioc` on a width-`q`
interval, with no integer division involved.

**(b) A degenerate instance — `q·A` is at most the right-hand side.**
Instantiate `hvino` at `α' = β' = θ' = 0`, `u = -1/2`, `v = q - 3/4`.  Every
summand is then exactly `A` — the sine vanishes identically, so the *first*
branch of the `if` fires — there are exactly `q` terms, and `v - u = q - 1/4 < q`
forces the covering count to be exactly `1`.  The instance reads

    q·A ≤ 2A + (2/π) B q log 4q.

Chaining (a) and (b) proves the claim.

Note that step (b) uses `hvino` only at the admissible choice `a' = β' = 0`; no
coprimality hypothesis and no analytic input beyond `hvino` itself enters the
argument, which is why `halpha` and `hbeta` go unused.  The statement thereby
holds for every `α` and `θ`, uniformly — the sharp count-1 form is "cheap"
precisely because it pays `A` per term rather than exploiting cancellation.

Auxiliary lemmas are proof-local: the reindexing and the degenerate instance
carry no independent reuse value, so they live here rather than in a definition
module. -/

/-- The summand, with the source's convention at the zeros of the sine: the
mathematically correct value there is `A`, and Lean's real division would return
`0` (so a bare `min` would silently vanish). -/
noncomputable def blkSummand (A B alpha theta : ℝ) (n : ℤ) : ℝ :=
  if Real.sin (Real.pi * alpha * (n : ℝ) + theta) = 0 then A
  else min A (B / |Real.sin (Real.pi * alpha * (n : ℝ) + theta)|)

/-- Each summand is at most `A`. -/
lemma blkSummand_le_A (A B alpha theta : ℝ) (n : ℤ) : blkSummand A B alpha theta n ≤ A := by
  unfold blkSummand
  by_cases h : Real.sin (Real.pi * alpha * (n : ℝ) + theta) = 0
  · rw [if_pos h]
  · rw [if_neg h]
    exact min_le_left _ _

/-- **The reindexing at the level of the summand.**  The odd integer `2m+1` sees
the doubled frequency `2α` and the shifted phase `πα + θ`. -/
lemma blkSummand_odd (A B alpha theta : ℝ) (m : ℤ) :
    blkSummand A B alpha theta (2 * m + 1)
      = blkSummand A B (2 * alpha) (Real.pi * alpha + theta) m := by
  unfold blkSummand
  have harg : Real.pi * alpha * ((2 * m + 1 : ℤ) : ℝ) + theta
      = Real.pi * (2 * alpha) * (m : ℝ) + (Real.pi * alpha + theta) := by
    push_cast
    ring
  rw [harg]

/-! ## Floor and interval bookkeeping -/

/-- `Ioc ⌊x⌋ b` is `Icc (⌊x⌋+1) b` over `ℤ`. -/
lemma ioc_floor_eq_icc (x : ℝ) (b : ℤ) :
    Finset.Ioc ⌊x⌋ b = Finset.Icc (⌊x⌋ + 1) b := by
  ext z
  rw [Finset.mem_Ioc, Finset.mem_Icc]
  omega

/-- `⌊(x-1)/2⌋ = (⌊x⌋-1)/2`. -/
lemma floor_sub_one_div_two (x : ℝ) : ⌊(x - 1) / 2⌋ = (⌊x⌋ - 1) / 2 := by
  have h : (x - 1) / 2 = (x - 1) / ((2 : ℕ) : ℝ) := by norm_num
  rw [h, Int.floor_div_natCast]
  rw [show x - 1 = x + ((-1 : ℤ) : ℝ) by push_cast; ring, Int.floor_add_intCast]
  ring_nf

/-- `⌊x⌋ + 1 ≤ z` implies `x < z`. -/
lemma real_lt_of_floor_add_one_le (z : ℤ) (x : ℝ) (h : ⌊x⌋ + 1 ≤ z) : x < (z : ℝ) := by
  have h1 : x < ((⌊x⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one x
  have h2 : ((⌊x⌋ : ℤ) : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast h
  linarith

/-- `z ≤ ⌊y⌋` implies `z ≤ y`. -/
lemma real_le_of_le_floor (z : ℤ) (y : ℝ) (h : z ≤ ⌊y⌋) : (z : ℝ) ≤ y := by
  have h1 : ((⌊y⌋ : ℤ) : ℝ) ≤ y := Int.floor_le y
  have h2 : (z : ℝ) ≤ ((⌊y⌋ : ℤ) : ℝ) := by exact_mod_cast h
  linarith

/-- **Lower half of the reindexing.**  For odd `z` with `x < z`,
`⌊(x-1)/2⌋ + 1 ≤ (z-1)/2`.  Oddness is essential: for even `z` the statement is
false (take `x = 5`, `z = 6`), so the reindexing is applied only to the odd
filtered range. -/
lemma floor_lower_of_lt (z : ℤ) (x : ℝ) (hodd : Odd z) (hz : x < (z : ℝ)) :
    ⌊(x - 1) / 2⌋ + 1 ≤ (z - 1) / 2 := by
  obtain ⟨k, rfl⟩ := hodd
  rw [show (2 * k + 1 - 1) / 2 = k by omega]
  have hf : ⌊(x - 1) / 2⌋ < k := by
    rw [Int.floor_lt]
    have h2 : ((2 * k + 1 : ℤ) : ℝ) = 2 * (k : ℝ) + 1 := by push_cast; ring
    rw [h2] at hz
    linarith
  omega

/-- **Upper half of the reindexing.**  For integral `z ≤ y`,
`(z-1)/2 ≤ ⌊(y-1)/2⌋`. -/
lemma floor_upper_of_le (z : ℤ) (y : ℝ) (hz : (z : ℝ) ≤ y) :
    (z - 1) / 2 ≤ ⌊(y - 1) / 2⌋ := by
  rw [floor_sub_one_div_two y]
  have h : z ≤ ⌊y⌋ := by rw [Int.le_floor]; exact hz
  exact Int.ediv_le_ediv (by norm_num : (0 : ℤ) < 2) (by omega : z - 1 ≤ ⌊y⌋ - 1)

/-- **The reindexing `n = 2m + 1`.**  Summation over the odd integers of
`(x, y]` equals summation over all integers of `((x-1)/2, (y-1)/2]` composed
with `m ↦ 2m+1`. -/
lemma odd_sum_reindex (f : ℤ → ℝ) (x y : ℝ) :
    (∑ z ∈ (Finset.Ioc ⌊x⌋ ⌊y⌋).filter (fun z => Odd z), f z)
      = ∑ m ∈ Finset.Ioc ⌊(x - 1) / 2⌋ ⌊(y - 1) / 2⌋, f (2 * m + 1) := by
  rw [ioc_floor_eq_icc, ioc_floor_eq_icc]
  refine Finset.sum_bij (fun z _ => (z - 1) / 2) ?hmem ?hinj ?hsurj ?hval
  · intro z hz
    rw [Finset.mem_filter, Finset.mem_Icc] at hz
    obtain ⟨⟨hz1, hz2⟩, hodd⟩ := hz
    rw [Finset.mem_Icc]
    exact ⟨floor_lower_of_lt z x hodd (real_lt_of_floor_add_one_le z x hz1),
           floor_upper_of_le z y (real_le_of_le_floor z y hz2)⟩
  · intro z hz z' hz' heq
    rw [Finset.mem_filter] at hz hz'
    obtain ⟨k, hk⟩ := hz.2
    obtain ⟨k', hk'⟩ := hz'.2
    omega
  · intro m hm
    rw [Finset.mem_Icc] at hm
    refine ⟨2 * m + 1, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ⟨m, rfl⟩⟩
      · have h := hm.1
        rw [floor_sub_one_div_two x] at h
        have h2 : ((⌊x⌋ - 1) / 2 + 1) = (⌊x⌋ + 1) / 2 := by
          rw [show (⌊x⌋ - 1) / 2 + 1 = ((⌊x⌋ - 1) + 2) / 2 by
            rw [Int.add_ediv_of_dvd_right] <;> norm_num]
          rw [show (⌊x⌋ - 1) + 2 = ⌊x⌋ + 1 by ring]
        rw [h2] at h
        rw [Int.ediv_le_iff_le_mul (by norm_num : (0 : ℤ) < 2)] at h
        omega
      · have h := hm.2
        rw [floor_sub_one_div_two y] at h
        omega
    · omega
  · intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨k, hk⟩ := hz.2
    congr 1
    omega

/-- A half-open integer range of width `q` contains exactly `q` integers. -/
lemma card_Ioc_width_q (lo : ℤ) (q : ℕ) :
    (Finset.Ioc lo (lo + (q : ℤ))).card = q := by
  rw [Int.card_Ioc]
  have : lo + (q : ℤ) - lo = (q : ℤ) := by ring
  rw [this]
  simp

/-- `⌊-1/2⌋ = -1`. -/
lemma floor_neg_half : ⌊(-(1 : ℝ) / 2)⌋ = (-1 : ℤ) := by
  rw [Int.floor_eq_iff]
  norm_num

/-- `⌊(q : ℝ) - 3/4⌋ = (q : ℤ) - 1`. -/
lemma floor_sub_three_quarters (q : ℕ) : ⌊((q : ℝ) - 3 / 4)⌋ = (q : ℤ) - 1 := by
  rw [Int.floor_eq_iff]
  constructor <;> push_cast <;> linarith

/-- At `α' = θ' = 0` every summand is exactly `A`. -/
lemma degenerate_summand (A B : ℝ) (n : ℤ) : blkSummand A B 0 0 n = A := by
  unfold blkSummand
  have hs : Real.sin (Real.pi * 0 * (n : ℝ) + 0) = 0 := by simp
  rw [if_pos hs]

/-- **The numerical bound `q·A ≤ 2A + (2/π)Bq log 4q`, extracted from `hvino` by
a degenerate instance.**

Take `α' = β' = θ' = 0`, `u = -1/2`, `v = q - 3/4`.  The instance has exactly `q`
terms (the integers `-1 < n ≤ q-1`), each equal to `A`, and its covering count is
`⌊(q - 1/4)/q⌋ + 1 = 1` because `q - 1/4 < q`. -/
lemma qA_le_rhs
    (A B : ℝ) (q : ℕ) (hq : 0 < q)
    (hvino : ∀ (alpha' beta' theta' u v : ℝ) (a' : ℤ),
        alpha' = (a' : ℝ) / q + beta' → |beta'| ≤ 1 / (q : ℝ) ^ 2 → u < v →
        (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋, blkSummand A B alpha' theta' n)
          ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
              * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q))) :
    (q : ℝ) * A ≤ 2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q) := by
  let u : ℝ := -(1 : ℝ) / 2
  let v : ℝ := (q : ℝ) - 3 / 4
  have huv : u < v := by
    dsimp [u, v]
    have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hv := hvino 0 0 0 u v 0 (by simp) (by simp) huv
  have hsum : (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋, blkSummand A B 0 0 n) = (q : ℝ) * A := by
    have hfu : ⌊u⌋ = (-1 : ℤ) := by simpa [u] using floor_neg_half
    have hfv : ⌊v⌋ = (q : ℤ) - 1 := by simpa [v] using floor_sub_three_quarters q
    rw [hfu, hfv]
    have hcard : (Finset.Ioc (-1 : ℤ) ((q : ℤ) - 1)).card = q := by
      rw [Int.card_Ioc]
      have : (q : ℤ) - 1 - (-1 : ℤ) = (q : ℤ) := by ring
      rw [this]
      simp
    calc
      (∑ n ∈ Finset.Ioc (-1 : ℤ) ((q : ℤ) - 1), blkSummand A B 0 0 n)
          = ∑ n ∈ Finset.Ioc (-1 : ℤ) ((q : ℤ) - 1), A := by
              apply Finset.sum_congr rfl
              intro n _
              exact degenerate_summand A B n
      _ = ((Finset.Ioc (-1 : ℤ) ((q : ℤ) - 1)).card : ℝ) * A := by simp
      _ = (q : ℝ) * A := by rw [hcard]
  have hcnt : ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
        * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q))
      = 2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q) := by
    have hfloor : ⌊(v - u) / (q : ℝ)⌋ = (0 : ℤ) := by
      rw [Int.floor_eq_zero_iff]
      constructor
      · dsimp [u, v]
        positivity
      · rw [div_lt_one (by exact_mod_cast hq : (0 : ℝ) < (q : ℕ))]
        dsimp [u, v]
        have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
        linarith
    rw [hfloor]
    norm_num
  rw [hsum, hcnt] at hv
  exact hv

/-- **Corollary 3.5 at the sharp block count.** -/
theorem solution
    (A B : ℝ) (alpha beta theta : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (halpha : 2 * alpha = (a : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvino : ∀ (alpha' beta' theta' u v : ℝ) (a' : ℤ),
        alpha' = (a' : ℝ) / q + beta' → |beta'| ≤ 1 / (q : ℝ) ^ 2 → u < v →
        (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
            (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A
              else min A (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
          ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
              * (2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)))
    (x y : ℝ) (hwidth : y ≤ x + 2 * (q : ℝ)) :
    (∑ n ∈ (Finset.Ioc ⌊x⌋ ⌊y⌋).filter (fun n : ℤ => Odd n),
        (if Real.sin (Real.pi * alpha * (n : ℝ) + theta) = 0 then A
          else min A (B / |Real.sin (Real.pi * alpha * (n : ℝ) + theta)|)))
      ≤ 2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q) := by
  change (∑ n ∈ (Finset.Ioc ⌊x⌋ ⌊y⌋).filter (fun n : ℤ => Odd n),
        blkSummand A B alpha theta n)
      ≤ 2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)
  -- (a) Reindex `n = 2m+1`; the odd range of width `2q` becomes a full range of
  -- width `q`, at doubled frequency and shifted phase.
  rw [odd_sum_reindex (blkSummand A B alpha theta) x y]
  have hcongr : (∑ m ∈ Finset.Ioc ⌊(x - 1) / 2⌋ ⌊(y - 1) / 2⌋,
        blkSummand A B alpha theta (2 * m + 1))
      = ∑ m ∈ Finset.Ioc ⌊(x - 1) / 2⌋ ⌊(y - 1) / 2⌋,
          blkSummand A B (2 * alpha) (Real.pi * alpha + theta) m := by
    apply Finset.sum_congr rfl
    intro m _
    exact blkSummand_odd A B alpha theta m
  rw [hcongr]
  let S : Finset ℤ := Finset.Ioc ⌊(x - 1) / 2⌋ ⌊(y - 1) / 2⌋
  let big : Finset ℤ := Finset.Ioc ⌊((x - 1) / 2)⌋ (⌊((x - 1) / 2)⌋ + (q : ℤ))
  change (∑ m ∈ S, blkSummand A B (2 * alpha) (Real.pi * alpha + theta) m)
      ≤ 2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)
  -- The reindexed range has width `(y-x)/2 ≤ q`, hence sits in a width-`q`
  -- integer interval, which has exactly `q` elements.
  have hw' : (y - 1) / 2 ≤ (x - 1) / 2 + (q : ℝ) := by linarith
  have hvle : ⌊(y - 1) / 2⌋ ≤ ⌊(x - 1) / 2⌋ + (q : ℤ) := by
    have hmono : ⌊(y - 1) / 2⌋ ≤ ⌊(x - 1) / 2 + (q : ℝ)⌋ := Int.floor_mono hw'
    have hadd : ⌊(x - 1) / 2 + (q : ℝ)⌋ = ⌊(x - 1) / 2⌋ + (q : ℤ) := by
      exact Int.floor_add_intCast ((x - 1) / 2) q
    simpa [hadd] using hmono
  have hsub : S ⊆ big := by
    intro m hm
    rw [Finset.mem_Ioc] at hm ⊢
    exact ⟨hm.1, le_trans hm.2 hvle⟩
  have hcardS : S.card ≤ q := by
    have hcardbig : big.card = q := by
      dsimp [big]
      exact card_Ioc_width_q ⌊((x - 1) / 2)⌋ q
    calc
      S.card ≤ big.card := Finset.card_le_card hsub
      _ = q := hcardbig
  -- Every summand is at most `A`, so the sum is at most `S.card · A ≤ q · A`.
  have hsum_le : (∑ m ∈ S, blkSummand A B (2 * alpha) (Real.pi * alpha + theta) m)
      ≤ (S.card : ℝ) * A := by
    have h := Finset.sum_le_card_nsmul S
      (blkSummand A B (2 * alpha) (Real.pi * alpha + theta)) A
      (by intro m hm; exact blkSummand_le_A A B (2 * alpha) (Real.pi * alpha + theta) m)
    simpa [nsmul_eq_mul] using h
  have hqA : (S.card : ℝ) * A ≤ (q : ℝ) * A := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcardS) hA
  -- (b) `q·A ≤ 2A + (2/π)Bq log 4q` from the degenerate instance of `hvino`.
  have hnum := qA_le_rhs A B q hq hvino
  exact le_trans hsum_le (le_trans hqA hnum)

