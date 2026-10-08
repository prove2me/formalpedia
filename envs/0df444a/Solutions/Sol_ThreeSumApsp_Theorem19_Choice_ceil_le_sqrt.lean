-- Prove2me | solution 1 for ThreeSumApsp.Theorem19.Choice.ceil_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:24:05.14099+00:00
-- url     : https://prove2.me/submissions/1cf93e4f-2498-4550-b2ca-1d86b876fd91

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Theorem19_Choice
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Log
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



/-!
# The cost analysis of Theorem 19 for a general choice of the parameters

The two halves of the proof of Theorem 19 are the same computation with different numbers.  Both
apply Theorem 17 with a number `D ≥ 16` between `n^{1/18}/c` and `n^{1/18}` and with `g = ⌈D^η⌉`,
and solve each of the at most `4ng` instances with a saving `D^{2η}`.  Such a pair `D`, `η` is a
`Choice`, and the computation is carried out here for every choice.

1. A choice satisfies the hypotheses `16 ≤ D ≤ n` and `1 ≤ g ≤ √D` of Theorem 17 and the hypothesis
   `D^18 ≤ n` of Corollaries 15 and 16 (`Choice.sixteen_le`, `Choice.le_n`, `Choice.one_le_ceil`,
   `Choice.ceil_le_sqrt`, `Choice.pow_eighteen_le`).
2. The lower bound on `D` gives `D^{-η} ≤ c^η n^{-η/18}` (`Choice.saving`), and the upper bound
   gives `D^a ≤ n^{a/18}` (`Choice.rpow_le_rpow_div`).
3. Each of the four terms of the running time is `O(n^{3-η/18})` up to logarithms: the instances
   (`Choice.instances_le`) and the scans (`Choice.scans_le`) by the first bound, the choice of `p`
   (`Choice.strassen_le`) and building the instances (`Choice.build_le`) by the second.
4. So is their sum (`exists_total_le`).
-/

@[expose] public section

namespace ThreeSumApsp

namespace Theorem19


























namespace Choice

variable {n D : ℕ} {η c : ℝ} (P : Choice n D η c)
include P

/-! ### The hypotheses of Theorem 17 and of Corollaries 15 and 16 -/









private theorem one_le_D : (1 : ℝ) ≤ D :=
  Nat.one_le_cast.mpr (le_trans (by norm_num) P.sixteen_le)

private theorem D_pos : (0 : ℝ) < D :=
  zero_lt_one.trans_le P.one_le_D







private theorem one_le_rpow : 1 ≤ (D : ℝ) ^ η :=
  Real.one_le_rpow P.one_le_D P.η_nonneg





/-- `g ≤ 2 D^η`: rounding up a number that is at least 1 at most doubles it. -/
private theorem ceil_le : (⌈(D : ℝ) ^ η⌉₊ : ℝ) ≤ 2 * (D : ℝ) ^ η :=
  Nat.ceil_le_two_mul ((by norm_num : (2 : ℝ)⁻¹ ≤ 1).trans P.one_le_rpow)

/-- `g ≤ √D`, as Theorem 17 asks: with `r = D^{1/4} ≥ 2` we have `g ≤ 2 D^η ≤ 2r ≤ r² = √D`. -/
theorem ceil_le_sqrt_sourceProof : (⌈(D : ℝ) ^ η⌉₊ : ℝ) ≤ √(D : ℝ) := by
  have htwo : (2 : ℝ) ≤ (D : ℝ) ^ (1 / 4 : ℝ) :=
    calc (2 : ℝ) = (16 : ℝ) ^ (1 / 4 : ℝ) := by
          rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ (D : ℝ) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) (by exact_mod_cast P.sixteen_le) (by norm_num)
  calc (⌈(D : ℝ) ^ η⌉₊ : ℝ) ≤ 2 * (D : ℝ) ^ η := P.ceil_le
    _ ≤ 2 * (D : ℝ) ^ (1 / 4 : ℝ) := by
        gcongr
        exacts [P.one_le_D, P.η_le]
    _ ≤ (D : ℝ) ^ (1 / 4 : ℝ) * (D : ℝ) ^ (1 / 4 : ℝ) := by gcongr
    _ = √(D : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add P.D_pos]
        norm_num

/-! ### Logarithms -/









/-! ### Powers of `D` in terms of `n` -/



































/-! ### The four terms of the running time

`Λ` is the logarithmic factor of the result, `log² n` or `log n`. -/






































































end Choice










































end Theorem19

end ThreeSumApsp

end


theorem solution : ∀ {n D : Nat} {η c : Real},
  ThreeSumApsp.Theorem19.Choice n D η c →
    @LE.le.{0} Real Real.instLE
      (@Nat.cast.{0} Real Real.instNatCast
        (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
          (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast D) η)))
      (@Nat.cast.{0} Real Real.instNatCast D).sqrt := by
  exact @ThreeSumApsp.Theorem19.Choice.ceil_le_sqrt_sourceProof

#print axioms solution
