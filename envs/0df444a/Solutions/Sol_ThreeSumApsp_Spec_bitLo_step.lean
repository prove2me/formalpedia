-- Prove2me | solution 1 for ThreeSumApsp.Spec.bitLo_step
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:04:27.997155+00:00
-- url     : https://prove2.me/submissions/e245c771-5b42-458b-8d83-4f8434f2c7a0

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem21b_BitSearch
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



/-!
# The entries of a (min,+)-product, found bit by bit

Theorem 21(b), after [VW18, Theorem 4.2]: the (min,+)-product is computed
by a binary search for all entries at once.  An entry `c` with `-2U ≤ c ≤ 2U` is approached from
below: `bitLo U t c` is `c` with the lowest `t` bits of `c + 2U` cleared.

* The search starts at `t = R`, where `4U < 2^R`, with `-2U` (`bitLo_top`), and it ends at `t = 0`
  with `c` (`bitLo_zero`).
* One round goes from `t + 1` to `t`: it asks whether `c < bitLo U (t + 1) c + 2^t` and adds `2^t`
  if not (`bitLo_step`).
* The question is whether the pair `(i, j)` has a witness: `c` is below a number exactly if one of
  the sums `A[i,k] + B[k,j]` is (`exists_sum_lt_iff`).  So one round for all entries is one call of
  a routine that finds all pairs with a witness.
-/

@[expose] public section

namespace ThreeSumApsp.Spec





































/-- Clearing one bit less: the bit number `t` of `y` is 0 exactly if `y` is less than `2^t` above
`y` with its lowest `t + 1` bits cleared. -/
private theorem div_mul_pow_step (y t : ℕ) :
    y / 2 ^ t * 2 ^ t = y / 2 ^ (t + 1) * 2 ^ (t + 1) +
      if y < y / 2 ^ (t + 1) * 2 ^ (t + 1) + 2 ^ t then 0 else 2 ^ t := by
  have hp : 0 < 2 ^ t := by positivity
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  generalize 2 ^ t = p at hp
  have hlow : y / p * p ≤ y := Nat.div_mul_le_self y p
  have hhigh : y < y / p * p + p := Nat.lt_div_mul_add hp
  generalize y / p = q at hlow hhigh
  rcases Nat.even_or_odd' q with ⟨b, rfl | rfl⟩
  · rw [show 2 * b / 2 = b by omega, show b * (p * 2) = 2 * b * p by ring, if_pos hhigh,
      Nat.add_zero]
  · have hle : b * (p * 2) + p ≤ y := (show _ = (2 * b + 1) * p by ring).trans_le hlow
    rw [show (2 * b + 1) / 2 = b by omega, if_neg (not_lt.2 hle)]
    ring

/-- **One round of the search**: `bitLo U t c` is `bitLo U (t + 1) c`, plus `2^t` unless
`c < bitLo U (t + 1) c + 2^t`. -/
theorem bitLo_step_sourceProof {U c : ℤ} (h : -(2 * U) ≤ c) (t : ℕ) :
    bitLo U t c = bitLo U (t + 1) c + 2 ^ t * (1 - flag (c < bitLo U (t + 1) c + 2 ^ t)) := by
  have hy : ((c + 2 * U).toNat : ℤ) = c + 2 * U := Int.toNat_of_nonneg (by linarith)
  have hstep := div_mul_pow_step (c + 2 * U).toNat t
  have hpow : ((2 ^ t : ℕ) : ℤ) = 2 ^ t := by push_cast; rfl
  simp only [bitLo, hstep]
  generalize (c + 2 * U).toNat = y at hy
  generalize y / 2 ^ (t + 1) * 2 ^ (t + 1) = z
  rw [← hpow]
  generalize 2 ^ t = p
  -- With `y = c + 2U` the question is whether `y < z + 2^t`.
  split_ifs with hlt
  · rw [flag_of (by omega)]
    push_cast
    ring
  · rw [flag_of_not (by omega)]
    push_cast
    ring

end ThreeSumApsp.Spec

end


theorem solution : ∀ {U c : Int},
  @LE.le.{0} Int Int.instLEInt
      (@Neg.neg.{0} Int Int.instNegInt
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) U))
      c →
    ∀ (t : Nat),
      @Eq.{1} Int (ThreeSumApsp.Spec.bitLo U t c)
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (ThreeSumApsp.Spec.bitLo U
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            c)
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
            (@HPow.hPow.{0, 0, 0} Int Nat Int
              (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) t)
            (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (ThreeSumApsp.flag
                (@LT.lt.{0} Int Int.instLTInt c
                  (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                    (ThreeSumApsp.Spec.bitLo U
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      c)
                    (@HPow.hPow.{0, 0, 0} Int Nat Int
                      (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                      (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) t))))))) := by
  exact @ThreeSumApsp.Spec.bitLo_step_sourceProof

#print axioms solution
