-- Prove2me | solution 1 for ThreeSumApsp.log_mem
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:24:11.467517+00:00
-- url     : https://prove2.me/submissions/3ff6021a-d30c-439c-9cdb-65226fc00fd3

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Table2_LogBounds
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



/-!
# The numerical toolkit for Table 2

Table 2 and the proof of Corollary 26 evaluate the exponents `q(θ)` and `γ = θ ln(1/ρ_c)/ln 4` of
Corollary 31 and the bound `R_c(γ)` of (11) at rational points. All three are built from logarithms
of rational numbers. This file turns each such claim into inequalities between rational numbers,
which the tactic `numerics` checks by evaluating both sides.

* `log_mem` encloses `log θ`: write `θ = 2^k (1 + x)/(1 - x)` with `2^k` near `θ`, and sum `n` terms
  of `log ((1 + x)/(1 - x)) = 2 (x + x³/3 + x⁵/5 + ⋯)`.
* `qOf_le` and `le_qOf` bound `q(θ)` at a rational `θ`.
* `gammaOf_one_mem`, `lnΛ_zero_mem`, `lt_Rc_of_lnΛ_zero_mem` and `Rc_lt_of_lnΛ_zero_mem` treat the
  two numbers on which a row of the table depends: `ln(1/ρ_c)/ln 4` and the denominator of (11) at
  `γ = 0`.
* `Table2Query.intro`, `Table2Ninth.intro` and `Table2Density.intro` give an entry of the table from
  two rational numbers that enclose its `θ`; the `θ` itself comes from the intermediate value
  theorem.
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## Logarithms of rational numbers -/







































private lemma log_two_mem : Real.log 2 ∈ Set.Icc logTwoLo logTwoHi :=
  ⟨Real.log_two_gt_d9.le, Real.log_two_lt_d9.le⟩

/-- The enclosure of `log θ`, between two rational numbers if `θ` is rational. It holds for every
`k` and `n`; they decide only how tight it is. -/
theorem log_mem_sourceProof (k : ℤ) (n : ℕ) {θ : ℝ} (hθ : 0 < θ := by norm_num [ThreeSumApsp.logApprox, ThreeSumApsp.logErr, ThreeSumApsp.seriesArg, ThreeSumApsp.logTwoLo,
                                                                                 ThreeSumApsp.logTwoHi, ThreeSumApsp.logThreeLo, ThreeSumApsp.logThreeHi, ThreeSumApsp.logTenLo, ThreeSumApsp.logTenHi,
                                                                                 Finset.sum_range_succ, ThreeSumApsp.rhoC]) :
    Real.log θ ∈ Set.Icc (logApprox k n θ - logErr k n θ) (logApprox k n θ + logErr k n θ) := by
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  have hx : |seriesArg k θ| < 1 := by
    rw [seriesArg, abs_div, abs_of_pos (add_pos hθ hpow), div_lt_one (add_pos hθ hpow), abs_lt]
    constructor <;> linarith
  have hsq : 0 < 1 - seriesArg k θ ^ 2 := sub_pos.2 ((sq_lt_one_iff_abs_lt_one _).2 hx)
  -- `log θ = k log 2 + log ((1 + x)/(1 - x))`
  have hlog : Real.log θ
      = k * Real.log 2 + Real.log ((1 + seriesArg k θ) / (1 - seriesArg k θ)) := by
    have hdiv : (1 + seriesArg k θ) / (1 - seriesArg k θ) = θ / 2 ^ k := by
      rw [seriesArg]
      field_simp
      ring
    rw [hdiv, Real.log_div hθ.ne' hpow.ne', Real.log_zpow]
    ring
  have htwo : |k * Real.log 2 - k * ((logTwoLo + logTwoHi) / 2)|
      ≤ |(k : ℝ)| * ((logTwoHi - logTwoLo) / 2) := by
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left (abs_le.2 ⟨?_, ?_⟩) (abs_nonneg _) <;>
      linarith [log_two_mem.1, log_two_mem.2]
  -- Mathlib: the sum of `n` terms differs from `½ log ((1 + x)/(1 - x))` by at most
  -- `|x|^(2n+1)/(1 - x²)`. We use `|x|^(2n+1) ≤ x^(2n)`, which is free of absolute values.
  have hseries := (Real.sum_range_sub_log_div_le hx n).trans
    (div_le_div_of_nonneg_right (pow_le_pow_of_le_one (abs_nonneg _) hx.le (Nat.le_succ _)) hsq.le)
  rw [(even_two_mul n).pow_abs] at hseries
  rw [abs_le] at htwo hseries
  rw [hlog, logApprox, logErr]
  constructor <;> linarith [htwo.1, htwo.2, hseries.1, hseries.2]







/-! ## The exponent `q` of the query time (Corollary 31) -/








































/-! ## The exponent `γ` (Corollary 31) -/




















/-! ## The bound `R_c(γ)` (equation (11)) -/

























































/-! ## Entries of Table 2

An entry needs two facts on its row, `hg` (an enclosure of `ln(1/ρ_c)/ln 4`) and `hR` (the `ε` of
the row is below `R_c(γ)` up to the largest `γ` of the row), and two rational numbers `θlo ≤ θhi`
that enclose its `θ`. -/


































































end ThreeSumApsp

end


theorem solution : ∀ (k : Int) (n : Nat) {θ : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) θ →
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (ThreeSumApsp.logApprox k n θ)
          (ThreeSumApsp.logErr k n θ))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (ThreeSumApsp.logApprox k n θ)
          (ThreeSumApsp.logErr k n θ)))
      (Real.log θ) := by
  exact @ThreeSumApsp.log_mem_sourceProof

#print axioms solution
