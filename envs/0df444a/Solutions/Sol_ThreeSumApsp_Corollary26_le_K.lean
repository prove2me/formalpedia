-- Prove2me | solution 1 for ThreeSumApsp.Corollary26.le_K
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:24:10.543985+00:00
-- url     : https://prove2.me/submissions/d1556a58-0662-44e9-b482-6b08796c3ae3

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Table2_LogBounds
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Choose
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
# Binomial coefficients

Upper bounds. A single summand of the binomial expansion of `(a + b) ^ n` is at most the whole sum
(`Nat.choose_mul_pow_mul_pow_le`); with `a = 1` this is `binom(n, k) * b ^ (n - k) ≤ (b + 1) ^ n`
(`Nat.choose_mul_pow_le`), which the paper uses with `b = 9`. And `binom(n, k) ≤ (e n / k) ^ k`
(`Nat.choose_le_exp_mul_div_pow`).

A lower bound. For `k ≤ n`, the largest of the `n + 1` terms `binom(n, j) k^j (n-k)^{n-j}` of the
expansion of `n^n = (k + (n-k))^n` is the one with `j = k`: the terms increase up to `j = k` and
decrease from there on. This gives the standard lower bound on a binomial coefficient
(`Nat.pow_self_le_mul_choose_mul_pow_mul_pow`), which Section 4.4 uses in the proof of Corollary 26
and, written with the entropy function as `e^{n H(k/n)}/(n+1) ≤ binom(n, k)`, in the proof of
Corollary 31.
-/

public section

namespace Nat

/-! ## Upper bounds -/

































/-! ## The largest term of a binomial expansion -/




/-- The quotient of two consecutive terms is `(n - j) k / ((n - k) (j + 1))`. -/
private theorem modeTerm_succ_mul {n j : ℕ} (k : ℕ) (hj : j < n) :
    modeTerm n k (j + 1) * ((n - k) * (j + 1)) = modeTerm n k j * ((n - j) * k) := by
  have he : n - j = n - (j + 1) + 1 := by omega
  calc modeTerm n k (j + 1) * ((n - k) * (j + 1))
      = n.choose (j + 1) * (j + 1) * k ^ (j + 1) * (n - k) ^ (n - (j + 1) + 1) := by
        rw [modeTerm]; ring
    _ = n.choose j * (n - j) * k ^ (j + 1) * (n - k) ^ (n - j) := by
        rw [Nat.choose_succ_right_eq, ← he]
    _ = modeTerm n k j * ((n - j) * k) := by rw [modeTerm]; ring

/-- The terms increase up to `j = k`. -/
private theorem modeTerm_le_succ {n k j : ℕ} (hjk : j < k) (hkn : k ≤ n) :
    modeTerm n k j ≤ modeTerm n k (j + 1) := by
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.mul_pos (by omega : 0 < n - j) (by omega : 0 < k))
  rw [← modeTerm_succ_mul k (by omega)]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))

/-- The terms decrease from `j = k` on. -/
private theorem modeTerm_succ_le {n k j : ℕ} (hkj : k ≤ j) (hjn : j < n) :
    modeTerm n k (j + 1) ≤ modeTerm n k j := by
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.mul_pos (by omega : 0 < n - k) j.succ_pos)
  rw [modeTerm_succ_mul k hjn]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))

/-- Every term is at most the term with `j = k`. -/
private theorem modeTerm_le_mode {n k j : ℕ} (hkn : k ≤ n) (hjn : j ≤ n) :
    modeTerm n k j ≤ modeTerm n k k := by
  rcases le_total j k with hjk | hkj
  · induction hjk using Nat.decreasingInduction with
    | self => rfl
    | of_succ j hjk ih => exact (modeTerm_le_succ hjk hkn).trans (ih (by omega))
  · induction j, hkj using Nat.le_induction with
    | base => rfl
    | succ j hkj ih => exact (modeTerm_succ_le hkj hjn).trans (ih (by omega))

/-- Proof of Corollary 26: "the standard bound binom(n, k) ≥ 1/(n+1) · n^n/(k^k (n-k)^{n-k})",
without fractions.  Of the `n + 1` terms of the expansion of `n^n = (k + (n-k))^n`, the one with
`binom(n, k)` is the largest. -/
theorem pow_self_le_mul_choose_mul_pow_mul_pow {n k : ℕ} (hkn : k ≤ n) :
    n ^ n ≤ (n + 1) * (n.choose k * k ^ k * (n - k) ^ (n - k)) :=
  calc n ^ n = (k + (n - k)) ^ n := by rw [Nat.add_sub_cancel' hkn]
    _ = ∑ j ∈ Finset.range (n + 1), modeTerm n k j := by
        rw [add_pow]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [modeTerm, Nat.cast_id]
        ring
    _ ≤ ∑ _j ∈ Finset.range (n + 1), modeTerm n k k :=
        Finset.sum_le_sum fun _ hj => modeTerm_le_mode hkn (Finset.mem_range_succ_iff.1 hj)
    _ = (n + 1) * (n.choose k * k ^ k * (n - k) ^ (n - k)) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, modeTerm]

end Nat

end



/-!
# Corollary 26: the parameters `L = 21m`, `t = ⌈m/9⌉`

The proof of Corollary 26 from Theorem 30, in the five steps of the paper. The parts of these steps
that hold for all `L` and `t` are proved before (`Corollary26.setting_up` to
`dominated_cost8_of_eq_10`), and Corollary 31 uses them too. The exponents `γ` and `q` of the proof
are written `gammaOf 21 (1 / 9)` and `qOf (1 / 9)`: they are the `γ` and `q` of Corollary 31 at
`c = 21` and `θ = 1/9` (`Corollary26.gamma_eq`, `Corollary26.q_eq`). The result is
`Corollary26.costs`: for `N ≥ D^18` and `m = ⌈log_4 D⌉ ≥ 60` the hypothesis `N ≥ √K N₀` of Theorem
30 holds at `L = 21m` and `t = ⌈m/9⌉`, its preprocessing cost (8) (`cost8`) is `O(N²/D^{0.063})`,
and its query cost `L ∑_{d ≤ t} α_d` (`costQuery`) is `O(D^{0.437})`.

* Setting up. The inner dimension is padded to `D = 4^m` (`Corollary26.setting_up`). This changes no
  entry of the product (`Corollary26.padding`), it changes the bounds by a constant factor
  (`padded_le`), and the hypothesis reads `N ≥ 4^{18(m-1)}` (`Corollary26.hypothesis`). The number
  `t = ⌈m/9⌉` is `switchOf (1 / 9) m`, and `t ≤ m` (`switchOf_le`).
* Boxes. `ρ < 9/20` and `ρ^t ≤ (9/20)^{m/9} = D^{-γ}` with `γ = 0.0640…` (`Corollary26.rho_lt`,
  `Corollary26.rho_pow_le`, `Corollary26.gamma_digits`), so the first term of (8) is `O(m² N²/D^γ)`
  (`Corollary26.first_term`).
* Queries. `∑_{d ≤ t} α_d ≤ 72^t (9/8)^m < 72 D^q` with `q = 0.4277…` (`sum_alpha_le`,
  `Corollary26.sum_alpha_lt`, `Corollary26.q_digits`), so a query costs `O(m D^q)`
  (`Corollary26.query_cost`).
* Encodings. Inequality (10) bounds the last term of (8) and gives the hypothesis of Theorem 30
  (`Equation10.last_term`, `Equation10.tile_fits`). The standard bound on `K` (`Corollary26.le_K`)
  shows that the left-hand side of (10) is at most `√(21m+1) Λ^m` (`Corollary26.lhs10_le`);
  `Λ = 4.198… · 10^10` is below `4^18 = 6.871… · 10^10` by a factor of more than 1.63
  (`baseLambda_numeric`, `four_pow_eighteen_numeric`, `baseLambda_mul_lt`), and
  `1.63^m ≥ 4^18 √(21m+1)` for `m ≥ 60` (`Corollary26.threshold`). Together they give (10) for all
  `m ≥ 60` (`eq_10_corollary_26`).
* Conclusion. For `m ≥ 60` the hypothesis `N ≥ √K N₀` holds and (8) is `O(m² N²/D^γ)`
  (`Corollary26.tile_fits`, `dominated_cost8_of_eq_10`, `Corollary26.preprocessing`), the powers of
  `m` are absorbed into the exponents (`dominated_pow_mul_D_rpow`, `Corollary26.conclusion`), and
  the bounds are stated in the given `D` (`Corollary26.costs`). For `|W| ≤ N²/√D` queries the total
  is `O(N²/D^{0.063})` (`corollary_26_W`).

Bounds "up to a constant" are written with `Dominated`, in the one parameter `m` or in the record
`Sizes` of the given `D`, of `N` and of `m`. Two sentences of the proof are proved with the programs
(`wordRam_corollary_26`, `wordRam_corollary_26_wanted`): "(For m < 60, D is bounded by a constant,
and the corollary holds trivially.)" and "The bound for a set W follows by asking |W| queries." The
last section shows that the parameters of this proof are those of Corollary 31 and of Table 2 at
`c = 21` and `θ = 1/9`; nothing else rests on it.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### Setting up -/








/-! ### Boxes -/






































































/-! ### Queries -/
































































/-! ### Encodings -/

/-- Proof of Corollary 26: "the standard bound [...] gives K = binom(21m, m) ≥ 1/(21m+1) ·
(21^21/20^20)^m". -/
theorem Corollary26.le_K_sourceProof {m : ℕ} (hm : 1 ≤ m) :
    ((21 : ℝ) ^ 21 / 20 ^ 20) ^ m / (21 * (m : ℝ) + 1) ≤ (K (21 * m) m : ℝ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  -- the standard bound at `n = 21m`, `k = m`
  have hstd : ((21 : ℝ) * m) ^ (21 * m)
      ≤ (21 * (m : ℝ) + 1) * ((K (21 * m) m : ℝ) * (m : ℝ) ^ m * ((20 : ℝ) * m) ^ (20 * m)) := by
    have h := Nat.pow_self_le_mul_choose_mul_pow_mul_pow (n := 21 * m) (k := m) (by omega)
    rw [show 21 * m - m = 20 * m by omega] at h
    unfold K
    exact_mod_cast h
  -- the powers of `m` cancel: `m^{21m} = m^m m^{20m}`
  have hsplit : (m : ℝ) ^ (21 * m) = (m : ℝ) ^ m * (m : ℝ) ^ (20 * m) := by
    rw [← pow_add]
    congr 1
    omega
  rw [mul_pow, mul_pow, hsplit] at hstd
  have hcancel : (21 : ℝ) ^ (21 * m)
      ≤ (K (21 * m) m : ℝ) * ((20 : ℝ) ^ (20 * m) * (21 * (m : ℝ) + 1)) := by
    refine le_of_mul_le_mul_right (hstd.trans_eq ?_)
      (show 0 < (m : ℝ) ^ m * (m : ℝ) ^ (20 * m) by positivity)
    ring
  rwa [div_pow, ← pow_mul, ← pow_mul, div_div, div_le_iff₀ (by positivity)]











































































































/-! ### Conclusion -/




























































































































/-! ### The parameters `c = 21` and `θ = 1/9` of Corollary 31 and Table 2

The sentence before Corollary 26 says: "It is the entry c = 21, q = 0.43 of Table 2". The parameters
of the proof above are those of Corollary 31 at `c = 21`, `θ = 1/9`: this holds for `L`
(`levelsOf_21`), for `γ` and `q` (`Corollary26.gamma_eq` and `Corollary26.q_eq` above), and for `Λ`
(`baseLambda_eq_exp_lnΛ`). The condition `ε < R_c(γ)` holds at `ε = 1/18` (`Corollary26.Rc_digits`),
and `N ≥ D^18` gives the condition `D ≤ N^{0.056}` of the row `c = 21` of the table, which is
`table_2_c21` (`Corollary26.row_condition`). Nothing else rests on this section. -/



























































end ThreeSumApsp

end


theorem solution : ∀ {m : Nat},
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) m →
    @LE.le.{0} Real Real.instLE
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@OfNat.ofNat.{0} Real (nat_lit 21)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 21) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))))))
              (@OfNat.ofNat.{0} Nat (nat_lit 21) (instOfNatNat (nat_lit 21))))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@OfNat.ofNat.{0} Real (nat_lit 20)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))))
              (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
          m)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 21)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 21) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))))))
            (@Nat.cast.{0} Real Real.instNatCast m))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      (@Nat.cast.{0} Real Real.instNatCast
        (ThreeSumApsp.K
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 21) (instOfNatNat (nat_lit 21))) m)
          m)) := by
  exact @ThreeSumApsp.Corollary26.le_K_sourceProof

#print axioms solution
