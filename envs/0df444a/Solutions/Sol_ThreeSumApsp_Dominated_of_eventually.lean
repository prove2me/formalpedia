-- Prove2me | solution 1 for ThreeSumApsp.Dominated.of_eventually
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:04:05.51236+00:00
-- url     : https://prove2.me/submissions/a108da8a-3e46-454e-9d4c-91ca1ee1dbb8

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Dominated
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



/-!
# Bounds up to a constant factor, in several parameters

The paper writes `f = O(g)` for functions of several parameters that are tied by side conditions,
such as `D ^ 18 ≤ n` for the parameters `n`, `D`, `w`. `Dominated dom f g` says this: there is a
constant `C ≥ 0` with `f x ≤ C * g x` for every tuple `x` of parameters that satisfies `dom x`. If
there is no side condition, `dom` is `fun _ => True`. The type `α` of the parameters is best a
structure with one named field for each of them, so that a bound reads
`Dominated (fun p => p.D ^ 18 ≤ p.n) (fun p => cost p) fun p => p.n ^ 2 / p.D`.

The lemmas of this file are the steps that the paper takes without comment: such bounds can be
chained (`Dominated.trans`), added (`Dominated.add`, `Dominated.add_add`), multiplied and divided
(`Dominated.mul`, `Dominated.mul_left`, `Dominated.const_mul`, `Dominated.pow`,
`Dominated.div_right`), joined by a case distinction (`Dominated.ite`), restricted to a smaller
domain (`Dominated.mono_dom`) and specialized (`Dominated.comp`). With them no proof has to name a
constant. A bound enters the calculus by `Dominated.of_le`, `Dominated.of_le_const_mul` or
`Dominated.of_exists_const`, and leaves it by `obtain ⟨C, hC, hle⟩` or `Dominated.exists_const_and`.
For functions of one natural number, `Dominated.of_eventually` takes a bound for all large `n`,
`Dominated.isBigO` gives Mathlib's `f =O[atTop] g`, and `isBigO_comp_add_one` substitutes a size
that need not tend to infinity.

In every closure lemma the bound comes first and the side conditions follow.

For nonnegative `f` and `g` the notion is Mathlib's `f =O[𝓟 {x | dom x}] g`, big-O along the
principal filter of the domain (`dominated_iff_isBigO_principal`). The one-sided form is taken
because a running time is bounded from above only.

## The notions of "bounded up to a constant" in this library

* `f =O[atTop] g` of Mathlib bounds `|f|` for large `n`. In this sense `IsBigOPow f a` is `O(n^a)`,
  `IsPowPolylog f a` is `O(n^a (log n)^e)` for some `e`, and `IsPowLittleO f a` is `n^{a+o(1)}`.
  The exponents of the theorems are stated with them.
* `UpperBigOPow`, `UpperPowPolylog` and `UpperPowLittleO` are the same three classes as bounds on
  `f` and not on `|f|`, for running times. A two-sided bound gives the one-sided one
  (`IsBigOPow.upperBigOPow`, `IsPowPolylog.upperPowPolylog`, `IsPowLittleO.upperPowLittleO`).
* `Dominated dom f g` bounds `f` on the whole domain, for several parameters. It comes from a bound
  for large `n` by `Dominated.of_eventually` and gives one by `Dominated.isBigO`.
* `Scale.SoftO t e` says that a count `t` with values in `ℕ` is `Dominated` by a monomial with the
  exponents `e`, up to powers of one more quantity; the tactic `growth` reads the exponents off an
  explicit expression. It gives a `Dominated` bound by `Scale.SoftO.dominated`. Its instance
  `SoftOSqrtPow` gives `IsPowPolylog` by `SoftOSqrtPow.isPowPolylog`.
-/

@[expose] public section

open Filter Asymptotics

namespace ThreeSumApsp






namespace Dominated

variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}

/-! ### Entering the calculus -/




































/-! ### Leaving the calculus -/











/-! ### Chaining, restricting, substituting -/



































/-! ### Sums and case distinctions -/































/-! ### Products and quotients -/
























































/-! ### Functions of one natural number -/

/-- A bound that holds from some unknown point on. If `g` is positive from `n₀` on, the finitely
many values in between cost only a larger constant. -/
theorem of_eventually_sourceProof {f g : ℕ → ℝ} {C : ℝ} (hfg : ∀ᶠ n in atTop, f n ≤ C * g n) {n₀ : ℕ}
    (hg : ∀ n, n₀ ≤ n → 0 < g n) : Dominated (fun n => n₀ ≤ n) f g := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hfg
  have hterm : ∀ m, 0 ≤ |f m| / |g m| := fun m => div_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsum : 0 ≤ ∑ m ∈ Finset.range N, |f m| / |g m| := Finset.sum_nonneg fun m _ => hterm m
  refine ⟨|C| + ∑ m ∈ Finset.range N, |f m| / |g m|, add_nonneg (abs_nonneg C) hsum, fun n hn => ?_⟩
  have hgn : 0 < g n := hg n hn
  rw [add_mul]
  obtain hlt | hge := lt_or_ge n N
  · calc f n ≤ |f n| / |g n| * g n := by
          rw [abs_of_pos hgn, div_mul_cancel₀ _ hgn.ne']
          exact le_abs_self _
      _ ≤ (∑ m ∈ Finset.range N, |f m| / |g m|) * g n :=
          mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun m => |f m| / |g m|)
            (fun m _ => hterm m) (Finset.mem_range.2 hlt)) hgn.le
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg (abs_nonneg C) hgn.le)
  · exact ((hN n hge).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hgn.le)).trans
      (le_add_of_nonneg_right (mul_nonneg hsum hgn.le))



















end Dominated












end ThreeSumApsp

end


theorem solution : ∀ {f g : Nat → Real} {C : Real},
  @Filter.Eventually.{0} Nat
      (fun (n : Nat) =>
        @LE.le.{0} Real Real.instLE (f n)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C (g n)))
      (@Filter.atTop.{0} Nat Nat.instPreorder) →
    ∀ {n₀ : Nat},
      (∀ (n : Nat),
          @LE.le.{0} Nat instLENat n₀ n →
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (g n)) →
        @ThreeSumApsp.Dominated.{0} Nat (fun (n : Nat) => @LE.le.{0} Nat instLENat n₀ n) f g := by
  exact @ThreeSumApsp.Dominated.of_eventually_sourceProof

#print axioms solution
