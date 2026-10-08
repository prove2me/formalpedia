-- Prove2me | solution 1 for ThreeSumApsp.goodTime_uniformTime
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:30:05.207415+00:00
-- url     : https://prove2.me/submissions/7f7f1d9b-0070-4061-9571-eb0ef4357e45

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Fin
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
# The arithmetic behind the running-time claims of Section 3

Elementary inequalities that the deductions between running-time claims use silently.

* `⌈n^{1/3}⌉ ≥ 1` and `(log s + 1)^e ≥ 1`.
* Thin instances, `n ≥ D^18` (Theorem 5, Corollaries 15, 16 and 26): the overheads `n D`, `n² / √D`
  and `1` are at most `n² / D^a`, and so at most the bounds `n² log² D / D^{1/18}` and
  `n² / D^{0.063}`.
* The pieces into which Corollary 15 splits `W` have at most `n² / √D` query pairs (`splitCap_le`).
-/

public section

namespace ThreeSumApsp

/-! ## Two quantities that are at least 1 -/





/-- `(log s + 1)^e ≥ 1`. -/
theorem one_le_log_add_one_pow (s e : ℕ) : 1 ≤ (Real.log s + 1) ^ e :=
  one_le_pow₀ (le_add_of_nonneg_left (Real.log_natCast_nonneg s))

/-! ## Thin instances: `n ≥ D^18` -/





























































/-! ## The pieces of Corollary 15 -/



































end ThreeSumApsp

end



/-!
# `logU`, the paper's `log U`

`logU u` is `log u`, read as `log 2` for `u < 2`.

* It is positive and nondecreasing, and `log (cu) ≤ log c + log u` for `c ≥ 1`.
* `log (cU) = O(log U)` (`dominated_logU_mul`) and `log (c n^κ) = O(log n)`
  (`dominated_logU_mul_rpow`).
* Along bounds `u(n) ≤ c n^κ` it is `Õ(1)` (`isPowPolylog_logU_of_le`).
-/

public section

namespace ThreeSumApsp

/-- `logU u ≥ log 2`. -/
theorem log_two_le_logU (u : ℝ) : Real.log 2 ≤ logU u :=
  Real.log_le_log two_pos (le_max_right _ _)

/-- `logU u > 0`. -/
theorem logU_pos (u : ℝ) : 0 < logU u :=
  (Real.log_pos one_lt_two).trans_le (log_two_le_logU u)

/-- `1 + logU u ≥ 1`. -/
theorem one_le_one_add_logU (u : ℝ) : 1 ≤ 1 + logU u :=
  le_add_of_nonneg_right (logU_pos u).le
































/-! ## `logU` of a multiple -/
























/-! ## `logU` along bounds that are polynomial in `n` -/

















end ThreeSumApsp

end



/-!
# Running-time claims of Section 3.4: Theorems 21 and 22

All lemmas are about an arbitrary interpretation `M : DetTimeModel` of "is solved in time T".  They
are deductions between running-time sentences: those of the paper for Theorem 22, and for
Theorem 21, which the paper cites, those of the route taken here.

* Theorem 21(a) from two reductions, [CH20, Theorem 5.1] followed by [VW13, Theorem 4.3]:
  `Theorem21a.of_CH20_VW13`.  The sizes, numbers of instances and extra times compose
  by the rules for `n^{a+o(1)}`.
* Theorem 21(b) for the (min,+)-product from [VW13, Theorem 3.3] and [VW18, Theorem 4.2]:
  `Theorem21b.minPlus_of_VW13_VW18`.  The time of the first reduction is again a good
  time (`GoodTime.mul_logU`), and `log (cU) = O(log U)` (`dominated_logU_mul`).
* Theorem 21(b) for APSP by repeated squaring: `Theorem21b.apsp_of_minPlus`, whose
  arithmetic is `dominated_repeatedSquaring`.
* "Plug Theorem 19 into Theorem 21": `threeSum_of_uniform_theorem_21a`,
  `minPlus_of_uniform_theorem_21b`, `apsp_of_uniform_theorem_21b`.
* Theorem 22: the roundings such as `n^{2-1/1296+o(1)} ≤ O(n^{1.99923})`
  (`Claim.SolvedAlongPow.mono`).
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## Theorem 21(a) -/




























/-! ## Theorem 21(b): the (min,+)-product -/
























































/-! ## Theorem 21(b): APSP -/







































































/-! ## "Plug Theorem 19 into Theorem 21"

The time of Theorem 19 is `uniformTime K δ e s u = K s^{3-δ} (log s + 1)^e (1 + log u)²`.
Theorem 21 evaluates it at sizes `s(n)` and bounds `u(n) ≤ c n^κ` on the numbers, and multiplies it
by powers of `n` and logarithms.  So each bound is a product of functions of known classes. -/

/-- The running time `K s^{3-δ} (log s + 1)^e (1 + log u)²` satisfies the requirements of
Theorem 21(b) as rendered by `GoodTime`: it is at least `s² (1 + log u)`, and divided by `s` it is
nondecreasing in `s` ("for which T(s)/s is nondecreasing"). -/
theorem goodTime_uniformTime_sourceProof {K δ : ℝ} (e : ℕ) (hK : 1 ≤ K) (hδ1 : δ ≤ 1) :
    GoodTime (uniformTime K δ e) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  refine ⟨fun s u hs => ?_, fun u s₁ s₂ hs₁ hs => ?_⟩
  · have hs1 : (1 : ℝ) ≤ s := Nat.one_le_cast.2 hs
    have hwords := one_le_one_add_logU u
    have hpow : (s : ℝ) ^ 2 ≤ (s : ℝ) ^ (3 - δ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hs1 (by push_cast; linarith)
    have hlog := one_le_log_add_one_pow s e
    calc (s : ℝ) ^ 2 * (1 + logU u) = 1 * ((s : ℝ) ^ 2 * 1 * (1 + logU u) ^ 1) := by ring
      _ ≤ K * ((s : ℝ) ^ (3 - δ) * (Real.log s + 1) ^ e * (1 + logU u) ^ 2) := by
          gcongr
          norm_num
  · -- `T(s)/s = K s^{2-δ} (log s + 1)^e (1 + log u)²`, and every factor is nondecreasing
    have hdiv : ∀ s : ℕ, 1 ≤ s → uniformTime K δ e s u / s
        = K * ((s : ℝ) ^ (2 - δ) * (Real.log s + 1) ^ e * (1 + logU u) ^ 2) := fun s hs => by
      have hs0 : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 hs)
      rw [uniformTime, show 3 - δ = 2 - δ + 1 by ring, Real.rpow_add_one hs0]
      field_simp
    have hs₁' : (0 : ℝ) < s₁ := Nat.cast_pos.2 hs₁
    have hlog : 0 ≤ Real.log s₁ + 1 := add_nonneg (Real.log_natCast_nonneg s₁) zero_le_one
    rw [hdiv _ hs₁, hdiv _ (hs₁.trans hs)]
    gcongr
    linarith





























































/-! ## Theorem 22 -/









end ThreeSumApsp

end


theorem solution : ∀ {K δ : Real} (e : Nat),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) K →
    @LE.le.{0} Real Real.instLE δ (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
      ThreeSumApsp.GoodTime (ThreeSumApsp.uniformTime K δ e) := by
  exact @ThreeSumApsp.goodTime_uniformTime_sourceProof

#print axioms solution
