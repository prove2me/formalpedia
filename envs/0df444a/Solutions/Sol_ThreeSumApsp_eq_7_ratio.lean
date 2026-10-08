-- Prove2me | solution 1 for ThreeSumApsp.eq_7_ratio
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:03:55.524467+00:00
-- url     : https://prove2.me/submissions/ae55cecb-36e6-4308-bc7b-97fbdf1593a3

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
import Mathlib.Analysis.Complex.Exponential
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
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
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
# Section 2.4.3, first half: the orders of the leaves and equation (5)

A leaf that contributes to an output string with inner set `Q` is free at the `m` levels of `Q` and
fixed at the other levels.  Its order is `m` minus the number of levels at which it chooses `P₀`.

* One level.  A term contributes to `z` exactly if `z = z₀` or the term is the private term of `z`
  (`Term.contributes_iff`), so a leaf contributing to a string chooses `P₀` only at levels of the
  inner set (`P0Levels_subset`).  The numbers of terms of each kind that contribute to a variable,
  and of variables of each kind to which a term contributes, are read off the ten terms.
* Counts.  `10^m` leaves contribute to a string: ten terms for each level of `Q`
  (`card_filter_contributes`).  The other counts sort strings by the set of levels at which they
  have a letter of a given kind (`Finset.card_pi_places_card`, `Finset.card_places_card`): `α_d` of
  the leaves contributing to a string have order `d` (`sec2_card_contributing_of_order`), the whole
  tree has `β_d` leaves of order `d` (`card_filter_order_eq`), with `β₀ = M` (`beta_zero_eq_M`), and
  a leaf of order `d` contributes to `binom(L-m+d, d)` strings (`sec2_card_outStr_of_leaf`). Figure
  6 shows these numbers for `L = 6` and `m = 2` (`figure_6`).
* Equation (5): the quotient `β_d / β_{d-1}` comes from the recurrence of the binomial coefficients
  (`Equation5.ratio_nat`, `eq_5_ratio`); for `L = 19m` it is less than `1/2` (`eq_5_bound`); so
  `β_d ≤ 2^{-d} M` by induction on `d` (`eq_5`).
-/

public section

open Finset

namespace ThreeSumApsp

/-! ### One level: which terms contribute to which variables -/











































/-! ### The order of a leaf -/









































/-! ### The counts -/










































































































/-- `β_d` is positive when `m ≤ L`. -/
theorem beta_pos {L m : ℕ} (hmL : m ≤ L) (d : ℕ) : 0 < beta L m d :=
  Nat.mul_pos (Nat.choose_pos (by omega)) (by positivity)

/-- The equality in equation (5) without division: `β_d (L-m+d) = 9 (m-d+1) β_{d-1}` for
`1 ≤ d ≤ m ≤ L`. -/
theorem Equation5.ratio_nat {L m : ℕ} (hmL : m ≤ L) (d : ℕ) (hd1 : 1 ≤ d) (hd : d ≤ m) :
    beta L m d * (L - m + d) = 9 * (m - d + 1) * beta L m (d - 1) := by
  -- With `k = m - d` this is `binom(L, k) (L - k) = binom(L, k + 1) (k + 1)`, times a power of 9.
  have hchoose : L.choose (m - d + 1) * (m - d + 1) = L.choose (m - d) * (L - m + d) := by
    rw [Nat.choose_succ_right_eq, show L - (m - d) = L - m + d by omega]
  have hpow : 9 ^ (L - m + d) = 9 * 9 ^ (L - m + (d - 1)) := by
    rw [show L - m + d = L - m + (d - 1) + 1 by omega, pow_succ, mul_comm]
  rw [beta, beta, show m - (d - 1) = m - d + 1 by omega, hpow]
  calc L.choose (m - d) * (9 * 9 ^ (L - m + (d - 1))) * (L - m + d)
      = 9 * 9 ^ (L - m + (d - 1)) * (L.choose (m - d) * (L - m + d)) := by ring
    _ = 9 * 9 ^ (L - m + (d - 1)) * (L.choose (m - d + 1) * (m - d + 1)) := by rw [hchoose]
    _ = 9 * (m - d + 1) * (L.choose (m - d + 1) * 9 ^ (L - m + (d - 1))) := by ring

/-- Section 2.4.3, the equality in equation (5), for every `L ≥ m` (it is used again as equation (7)
in Section 4.3): "β_d / β_{d-1} = 9(m-d+1) / (L-m+d)" for `1 ≤ d ≤ m`.

NOTE.  The paper prints the equality under `L = 19m` in (5) and under `L ≥ 10m` in (7); here it is
stated for every `L ≥ m`. -/
theorem eq_5_ratio {L m : ℕ} (hmL : m ≤ L) (d : ℕ) (hd1 : 1 ≤ d) (hd : d ≤ m) :
    (beta L m d : ℚ) / (beta L m (d - 1) : ℚ)
      = 9 * ((m : ℚ) - (d : ℚ) + 1) / ((L : ℚ) - (m : ℚ) + (d : ℚ)) := by
  have hm : (m : ℚ) ≤ L := by exact_mod_cast hmL
  have hd0 : (1 : ℚ) ≤ d := by exact_mod_cast hd1
  have hbeta : (0 : ℚ) < beta L m (d - 1) := by exact_mod_cast beta_pos hmL (d - 1)
  have hnat := congrArg (Nat.cast : ℕ → ℚ) (Equation5.ratio_nat hmL d hd1 hd)
  push_cast [Nat.cast_sub hmL, Nat.cast_sub hd] at hnat
  rw [div_eq_div_iff hbeta.ne' (by linarith), hnat]
















































end ThreeSumApsp

end



/-!
# Equation (7) and Theorem 30: the data structure (Section 4.3)

The running times of Theorem 30 on the word RAM are `wordRam_theorem_30` and
`wordRam_theorem_30_wanted`; the expressions inside their `O(·)` are `cost8`, `cost9` and
`costQuery`. This file has the mathematics of the paper's proof, in the paper's order.

* *The decay rate.* `ρ = 9m/(L-m+1)` is less than 1 (`sec4_rho_lt_one`), the ratio `β_d/β_{d-1}` is
  at most `ρ` (`eq_7_ratio`), and so `β_d ≤ ρ^d M` (`eq_7`). This is equation (7).
* *Preprocessing: the count behind (8).* Here `sqrtKN0 L m` is `√K N₀`. Padding at most doubles `N`
  (`Theorem30.padding`; nothing else rests on this lemma). The list of subsets takes `K L ≤ 10^L`
  operations (`Theorem30.subsets`), which the last term of (8) absorbs
  (`Theorem30.subsets_absorbed`). There are at most `4N/(√K N₀)` bands (`Theorem30.bands`), with `N`
  the given size, by a slightly finer count than `K₀ ≥ √K/2` gives (`Theorem30.numBands_mul_le`);
  the input array of a band has at most `K N₀ D ≤ 7^L` nonzero entries
  (`Theorem30.K_mul_N0_mul_D_le`), and `L · 7^L ≤ 2 · 10^L` (`Theorem30.form_array`). There are at
  most `4N²/M` tiles (`Theorem30.tiles`) with at most `(m+1) ∑_{d ≥ t} β_d` boxes each (Lemma 29),
  and `∑_{d ≥ t} β_d ≤ M ρ^t/(1-ρ)` by (7) (`Theorem30.sum_beta`), which bounds the number of all
  boxes (`Theorem30.boxes_total`). The boxes (`Theorem30.boxes_cost`), the bands
  (`Theorem30.bands_cost`) and the list add up to at most a constant times the expression in (8)
  (`Theorem30.cost8_assembly`).
* *Query.* The sum of Lemma 28 for the output string of the position `(I, J)` is `(XY)[I, J]` by
  Section 2.4.4 (`Theorem30.query`). Each box of that sum is a box of the tile (`Theorem30.lookup`),
  and the dynamic program of Lemma 29 has stored its value (`dpValue_card_starLevels`); so the query
  returns `(XY)[I, J]` (`Theorem30.correct`). Expression (9) is `|W|` queries on top of (8)
  (`Theorem30.cost9_eq`).
* *Word size.* `10^L ≤ N^{5/2}` (`Theorem30.ten_pow_le`).

Here `N` is the given size throughout, and the padded size is `padN L m N`.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### The decay rate `ρ` and equation (7) -/



















/-- Equation (7), first half: for `1 ≤ d ≤ m`,
`β_d / β_{d-1} = 9(m-d+1)/(L-m+d) ≤ 9m/(L-m+1) = ρ`. -/
theorem eq_7_ratio_sourceProof (L m d : ℕ) (hL : 10 * m ≤ L) (hd1 : 1 ≤ d) (hdm : d ≤ m) :
    (beta L m d : ℝ) / (beta L m (d - 1) : ℝ)
        = 9 * ((m : ℝ) - (d : ℝ) + 1) / ((L : ℝ) - (m : ℝ) + (d : ℝ)) ∧
      9 * ((m : ℝ) - (d : ℝ) + 1) / ((L : ℝ) - (m : ℝ) + (d : ℝ)) ≤ rho L m := by
  have hL' : (10 : ℝ) * m ≤ L := by exact_mod_cast hL
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hdm' : (d : ℝ) ≤ m := by exact_mod_cast hdm
  constructor
  · -- the ratio was computed for (5), in the rational numbers
    have hratio := congrArg (fun q : ℚ => (q : ℝ))
      (eq_5_ratio (L := L) (m := m) (by omega) d hd1 hdm)
    push_cast at hratio
    exact hratio
  · -- the numerator is at most `9m` and the denominator at least `L - m + 1`
    exact div_le_div₀ (by positivity) (by linarith) (by linarith) (by linarith)
















/-! ### Theorem 30, "Preprocessing": the count behind (8) -/










































































































































































































































/-! ### Theorem 30, "Query": a query returns `(XY)[I, J]` -/






























































/-! ### Theorem 30, "Word size" -/















end ThreeSumApsp

end


theorem solution : ∀ (L m d : Nat),
  @LE.le.{0} Nat instLENat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) m)
      L →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d →
      @LE.le.{0} Nat instLENat d m →
        And
          (@Eq.{1} Real
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@Nat.cast.{0} Real Real.instNatCast (ThreeSumApsp.beta L m d))
              (@Nat.cast.{0} Real Real.instNatCast
                (ThreeSumApsp.beta L m
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) d
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 9)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 9) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@Nat.cast.{0} Real Real.instNatCast m) (@Nat.cast.{0} Real Real.instNatCast d))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@Nat.cast.{0} Real Real.instNatCast L) (@Nat.cast.{0} Real Real.instNatCast m))
                (@Nat.cast.{0} Real Real.instNatCast d))))
          (@LE.le.{0} Real Real.instLE
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 9)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 9) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@Nat.cast.{0} Real Real.instNatCast m) (@Nat.cast.{0} Real Real.instNatCast d))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@Nat.cast.{0} Real Real.instNatCast L) (@Nat.cast.{0} Real Real.instNatCast m))
                (@Nat.cast.{0} Real Real.instNatCast d)))
            (ThreeSumApsp.rho L m)) := by
  exact @ThreeSumApsp.eq_7_ratio_sourceProof

#print axioms solution
