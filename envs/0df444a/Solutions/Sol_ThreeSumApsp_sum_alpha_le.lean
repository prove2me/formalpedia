-- Prove2me | solution 1 for ThreeSumApsp.sum_alpha_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T07:52:46.002342+00:00
-- url     : https://prove2.me/submissions/23cce61d-9a14-41a5-986b-29526a711715

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



/-!
# Section 4.4: the steps of the proof of Corollary 26 that hold for all parameters

The proof of Corollary 31 begins: "We repeat the proof of Corollary 26 with L := ⌈cm⌉ and t :=
⌈θm⌉". This file has the parts of the proof of Corollary 26 that mention neither `L = 21m` nor
`t = ⌈m/9⌉`, under the headings of that proof. Both corollaries use them.

* Setting up. The inner dimension is padded to `D = 4^m` with `m = ⌈log_4 D⌉`
  (`Corollary26.setting_up`). This changes no entry of the product (`Corollary26.padding`), and it
  changes the bounds by a constant factor (`padded_le`). The switching order `t = ⌈θm⌉` is
  `switchOf θ m`, and `t ≤ m` (`switchOf_le`).
* Queries. `∑_{d ≤ t} α_d ≤ (9x)^t (1 + 1/x)^m` for every `x ≥ 1/9` (`sum_alpha_le`), and for
  `x = (1-θ)/θ` the right-hand side at `t = θm` is `D^q` (`rpow_mul_pow_eq_D_rpow_qOf`).
* Encodings. Inequality (10), whose left-hand side is `lhs10 L m γ`, bounds the last term of (8) and
  gives the hypothesis `N ≥ √K N₀` of Theorem 30 (`Equation10.last_term`, `Equation10.tile_fits`).
* Conclusion. The expression (8) from a bound on its first term and (10)
  (`dominated_cost8_of_eq_10`).

Bounds "up to a constant" are written with `Dominated`, in the one parameter `m` or in the record
`Sizes` of the given inner dimension, of `N` and of `m`.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### Setting up -/








































































































/-! ### Queries -/

/-- Proof of Corollary 26, "Queries": "A query reads ∑_{d≤t} α_d numbers, and we bound this sum as
in the proof of Lemma 11. Since 9^d = 72^d 8^{-d} ≤ 72^t 8^{-d} for d ≤ t", the sum `∑_{d ≤ t} α_d`
is at most `72^t ∑_{d=0}^{m} binom(m, d) 8^{-d} = 72^t (9/8)^m`. Here any `x > 0` with `9x ≥ 1`
stands for 8, because the proof of Corollary 31 makes "the same calculation with x := (1-θ)/θ in
place of 8". -/
theorem sum_alpha_le_sourceProof {x : ℝ} (hx : 0 < x) (h9x : 1 ≤ 9 * x) {m t : ℕ} (htm : t ≤ m) :
    ∑ d ∈ range (t + 1), (alpha m d : ℝ) ≤ (9 * x) ^ t * (1 + 1 / x) ^ m := by
  -- `9^d = (9x)^d x^{-d} ≤ (9x)^t x^{-d}` for `d ≤ t`
  have hterm : ∀ d ∈ range (t + 1),
      (alpha m d : ℝ) ≤ (9 * x) ^ t * ((1 / x) ^ d * 1 ^ (m - d) * (m.choose d : ℝ)) := by
    intro d hd
    have hpow : (9 * x) ^ d ≤ (9 * x) ^ t :=
      pow_le_pow_right₀ h9x (by rw [mem_range] at hd; omega)
    calc (alpha m d : ℝ) = (9 * x) ^ d * ((1 / x) ^ d * 1 ^ (m - d) * (m.choose d : ℝ)) := by
          rw [alpha, one_pow, mul_one, ← mul_assoc, ← mul_pow,
            show 9 * x * (1 / x) = 9 by field_simp]
          push_cast
          ring
      _ ≤ (9 * x) ^ t * ((1 / x) ^ d * 1 ^ (m - d) * (m.choose d : ℝ)) := by gcongr
  calc ∑ d ∈ range (t + 1), (alpha m d : ℝ)
      ≤ ∑ d ∈ range (t + 1), (9 * x) ^ t * ((1 / x) ^ d * 1 ^ (m - d) * (m.choose d : ℝ)) :=
        sum_le_sum hterm
    _ ≤ ∑ d ∈ range (m + 1), (9 * x) ^ t * ((1 / x) ^ d * 1 ^ (m - d) * (m.choose d : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega))
          fun _ _ _ => by positivity
    _ = (9 * x) ^ t * (1 + 1 / x) ^ m := by rw [← mul_sum, ← add_pow, add_comm]














/-! ### Encodings -/






























/-! ### Conclusion -/























end ThreeSumApsp

end


theorem solution : ∀ {x : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) x →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 9)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 9) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
          x) →
      ∀ {m t : Nat},
        @LE.le.{0} Nat instLENat t m →
          @LE.le.{0} Real Real.instLE
            (∑
              d ∈
                Finset.range
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))),
              @Nat.cast.{0} Real Real.instNatCast (ThreeSumApsp.alpha m d))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 9)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 9) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
                  x)
                t)
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) x))
                m)) := by
  exact @ThreeSumApsp.sum_alpha_le_sourceProof

#print axioms solution
