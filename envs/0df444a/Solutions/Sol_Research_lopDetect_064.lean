-- Prove2me | solution 1 for Research.lopDetect_064
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-06T18:49:13.398653+00:00
-- url     : https://prove2.me/submissions/1ca642e0-b890-4c10-a5f4-52882f427b9b

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Realized
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Places
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Tiling_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Theorem19_Choice
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Table2_LogBounds
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Alphabets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Arrays
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Layout
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Subsets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Hashing
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Instances
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Statements_Exponents
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Corollary15_16
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Theorem19
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Theorem21_22
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Scale
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Ceil
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Digits
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_ThreeSumSource_ReductionClaims
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Init
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Count
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Iterate
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Range
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.Common
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Light_Sec3_claim_VW13_Theorem_3_3
import Theorems.Thm_Light_Sec3_claim_VW18_Theorem_4_2
import Theorems.Thm_Light_Sec3_claim_apspFromMinPlus
import Theorems.Thm_Light_Sec3_et17_spec
import Theorems.Thm_Light_Sec3_obeysBound17_hostTime
import Theorems.Thm_Light_Sec4_allInstances26_solves
import Theorems.Thm_Light_Sec4_allInstancesTime26_le
import Theorems.Thm_Light_Sec4_pre31_program31
import Theorems.Thm_Light_Sec4_queryAt_spec
import Theorems.Thm_Light_Sec4_specs40
import Theorems.Thm_Light_Wrap_realized
import Theorems.Thm_ThreeSumApsp_Dominated_of_eventually
import Theorems.Thm_ThreeSumApsp_FromClaims_solvedAt_of_realized
import Theorems.Thm_ThreeSumApsp_Theorem19_Choice_ceil_le_sqrt
import Theorems.Thm_ThreeSumApsp_WordRam_bigO_of_le_rpow
import Theorems.Thm_ThreeSumApsp_goodTime_uniformTime
import Theorems.Thm_TrulySubcubicAPSP_sourceSpecificationTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false



-- Original source module: StagedAPSPAccepted
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/



set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace EndStatement
end EndStatement
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

section


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

/-- A bound with an explicit nonnegative constant. -/
theorem of_le_const_mul {C : ℝ} (hC : 0 ≤ C) (hfg : ∀ x, dom x → f x ≤ C * g x) :
    Dominated dom f g :=
  ⟨C, hC, hfg⟩

/-- A bound with constant one. -/
theorem of_le (hfg : ∀ x, dom x → f x ≤ g x) : Dominated dom f g :=
  ⟨1, zero_le_one, fun x hx => by simpa only [one_mul] using hfg x hx⟩





/-- A bound with a constant of unknown sign, when `g` is nonnegative on the domain. -/
theorem of_exists_const (hfg : ∃ C : ℝ, ∀ x, dom x → f x ≤ C * g x) (hg : ∀ x, dom x → 0 ≤ g x) :
    Dominated dom f g := by
  obtain ⟨C, hC⟩ := hfg
  exact ⟨|C|, abs_nonneg C, fun x hx =>
    (hC x hx).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (hg x hx))⟩













/-! ### Leaving the calculus -/

/-- Two bounds, by nonnegative functions, hold with one constant. -/
theorem exists_const_and (h₁ : Dominated dom f₁ g₁) (h₂ : Dominated dom f₂ g₂)
    (hg₁ : ∀ x, dom x → 0 ≤ g₁ x) (hg₂ : ∀ x, dom x → 0 ≤ g₂ x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, dom x → f₁ x ≤ C * g₁ x ∧ f₂ x ≤ C * g₂ x := by
  obtain ⟨C, hC, h₁⟩ := h₁
  obtain ⟨D, hD, h₂⟩ := h₂
  exact ⟨C + D, add_nonneg hC hD, fun x hx =>
    ⟨(h₁ x hx).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) (hg₁ x hx)),
      (h₂ x hx).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (hg₂ x hx))⟩⟩

/-! ### Chaining, restricting, substituting -/

/-- `f = O(g)` and `g = O(h)` give `f = O(h)`. -/
protected theorem trans (hfg : Dominated dom f g) (hgh : Dominated dom g h) :
    Dominated dom f h := by
  obtain ⟨C, hC, hf⟩ := hfg
  obtain ⟨D, hD, hg⟩ := hgh
  refine ⟨C * D, mul_nonneg hC hD, fun x hx => (hf x hx).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hg x hx) hC

/-- A bound holds on every smaller domain. -/
theorem mono_dom (hfg : Dominated dom f g) (hdom : ∀ x, dom' x → dom x) : Dominated dom' f g := by
  obtain ⟨C, hC, hf⟩ := hfg
  exact ⟨C, hC, fun x hx => hf x (hdom x hx)⟩

/-- The left side may be replaced by a smaller function. -/
theorem mono_left (hfg : Dominated dom f g) (hle : ∀ x, dom x → f' x ≤ f x) : Dominated dom f' g :=
  (of_le hle).trans hfg

/-- The right side may be replaced by a larger function. -/
theorem mono_right (hfg : Dominated dom f g) (hle : ∀ x, dom x → g x ≤ g' x) : Dominated dom f g' :=
  hfg.trans (of_le hle)

/-- Both sides may be replaced by functions that agree with them on the domain. -/
protected theorem congr (hfg : Dominated dom f g) (hf : ∀ x, dom x → f x = f' x)
    (hg : ∀ x, dom x → g x = g' x) : Dominated dom f' g' :=
  (hfg.mono_left fun x hx => (hf x hx).ge).mono_right fun x hx => (hg x hx).le

/-- Substituting the parameters: a bound in `x` gives a bound in `y` at `x = φ y`, on every domain
that `φ` maps into `dom`. -/
protected theorem comp (hfg : Dominated dom f g) (φ : β → α) {dom' : β → Prop}
    (hφ : ∀ y, dom' y → dom (φ y)) : Dominated dom' (fun y => f (φ y)) fun y => g (φ y) := by
  obtain ⟨C, hC, hf⟩ := hfg
  exact ⟨C, hC, fun y hy => hf (φ y) (hφ y hy)⟩

/-! ### Sums and case distinctions -/

/-- `O(h) + O(h) = O(h)`. -/
protected theorem add (hf : Dominated dom f h) (hg : Dominated dom g h) :
    Dominated dom (fun x => f x + g x) h := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  refine ⟨C + D, add_nonneg hC hD, fun x hx => ?_⟩
  rw [add_mul]
  exact add_le_add (hf x hx) (hg x hx)









/-! ### Products and quotients -/








/-- A constant factor of any sign in front of a function that is nonnegative on the domain is
absorbed. -/
theorem const_mul_of_nonneg (hfg : Dominated dom f g) (c : ℝ) (hf : ∀ x, dom x → 0 ≤ f x) :
    Dominated dom (fun x => c * f x) g :=
  (of_exists_const ⟨c, fun _ _ => le_rfl⟩ hf).trans hfg

/-- Both sides may be multiplied from the left by a function that is nonnegative on the domain. -/
theorem mul_left (hfg : Dominated dom f g) (hk : ∀ x, dom x → 0 ≤ k x) :
    Dominated dom (fun x => k x * f x) fun x => k x * g x := by
  obtain ⟨C, hC, hf⟩ := hfg
  refine ⟨C, hC, fun x hx => ?_⟩
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hf x hx) (hk x hx)

/-- Both sides may be multiplied from the right by a function that is nonnegative on the domain. -/
theorem mul_right (hfg : Dominated dom f g) (hk : ∀ x, dom x → 0 ≤ k x) :
    Dominated dom (fun x => f x * k x) fun x => g x * k x := by
  simpa only [mul_comm] using hfg.mul_left hk








/-- `O(g) ^ e = O(g ^ e)` for nonnegative `f`. -/
protected theorem pow (hfg : Dominated dom f g) (hf : ∀ x, dom x → 0 ≤ f x) (e : ℕ) :
    Dominated dom (fun x => f x ^ e) fun x => g x ^ e := by
  obtain ⟨C, hC, hle⟩ := hfg
  refine ⟨C ^ e, pow_nonneg hC e, fun x hx => ?_⟩
  rw [← mul_pow]
  exact pow_le_pow_left₀ (hf x hx) (hle x hx) e

/-! ### Functions of one natural number -/


























end Dominated



end ThreeSumApsp

end
end

section


/-!
# Powers of `n` and of `log n` for large `n`

The facts behind the paper's `O(n^a)`, `Õ(n^a)` and `n^{a+o(1)}`, for functions of a natural number
`n` and in the language of Mathlib's `f =O[atTop] g`. Powers of `n` are monotone in the exponent
(`isBigO_rpow_rpow_of_le`, `isBigO_rpow_mul_log_pow_of_le`) and multiply by adding exponents
(`rpow_mul_rpow_eventuallyEq`). A constant or a power of `log n` is below every positive power of
`n` (`eventually_le_rpow`, `isLittleO_log_pow_rpow`). Hence `n ^ a * (log n) ^ e` is `o(n ^ b)` and
`O(n ^ b)` for `a < b` (`isLittleO_rpow_mul_log_pow_rpow`, `isBigO_rpow_mul_log_pow_rpow`), which is
where logarithms are absorbed for large `n`; with the constant absorbed too, this is
`eventually_mul_rpow_mul_log_pow_le`. The rounded power `⌈n ^ μ⌉` tends to infinity for `μ > 0`
(`tendsto_ceil_rpow_atTop`).
-/

public section

open Filter Asymptotics

namespace ThreeSumApsp

































end ThreeSumApsp

end
end

section


/-!
# The notions of solving are monotone

That the program `P` with slope `b` solves the problem on the instances in `dom` within time `T`, at
every admissible word size, stays true for a larger slope, a smaller set of instances and a larger
time bound (`Solves.mono`).  The same holds for a two-stage data structure (`IsDataStructure.mono`).

* The item statements on the problems of the end statement use `SolvesWithin`.  It is `Solves` for
  the problem `ofEnd Q`, whose instances carry their size and a bound on their numbers
  (`solvesWithin_iff`, `solvedInTimeAt_iff`).

* A statement "there are a program and a constant `C` such that the time is at most `C f(x)`" stays
  true for every bound `g` with `f = O(g)`: `exists_solves_of_dominated`, and
  `exists_isDataStructure_of_dominated` for a data structure.
* For the bounds `O(n^a (log n)^e)` in one size: a larger exponent (`SolvedInTime.mono_exponent`),
  and a larger exponent that absorbs the logarithms (`SolvedInPolylogTime.solvedInTime`).
-/

public section

namespace ThreeSumApsp.WordRam

open EndStatement (Instr)
open Filter

/-! ## The problems of the end statement as problems in the sense of `Problem` -/


































/-! ## Monotonicity -/





















/-! ## Bounds up to a constant -/
























/-! ## Bounds in one size -/

















end ThreeSumApsp.WordRam

end
end

section


/-!
# Proof rules for the light language

Ends lim P d s σ T Q says: the statement s, started in σ, ends within T steps in a state that
satisfies Q.  There is one rule for each construct; a rule turns a goal about a statement into goals
about its parts, so a proof follows the text of the program from top to bottom.  Recursion needs no
rule: a statement about a recursive procedure is proved by induction (in Lean) on a measure, and the
rule for calls unfolds the body.

There are three rules for loops: with an invariant indexed by the number of the round and a cost for
each round (Ends.while), the same with one cost for all rounds (Ends.whileConst), and, for a loop
whose number of rounds depends on the data, with a quantity that every round decreases
(Ends.whileVariant).

The file also has the basic facts about runs (a run stays a run when procedures are appended to the
program), notation for writing programs, the simplification set
`light_norm`, and the standing assumptions `Std` about the limits.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Runs -/

/-- A procedure of a program is a procedure, with the same number, of the program with more
procedures appended. -/
theorem getElem?_append_of_eq_some {P : Program} {p : ℕ} {body : Stmt} (h : P[p]? = some body)
    (R : Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h









/-- A run stays a run when procedures are appended to the program. -/
theorem Exec.append {s : Stmt} {σ σ' : State} {c : ℕ} (h : Exec lim P d s σ σ' c) (R : Program) :
    Exec lim (P ++ R) d s σ σ' c := by
  induction h with
  | skip => exact .skip
  | set h => exact .set h
  | store h₁ h₂ h₃ => exact .store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact .iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact .iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact .whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact .whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact .call h₁ (getElem?_append_of_eq_some h₂ R) h₃ ih

/-! ## The rules -/






/-- More time and a weaker conclusion. -/
theorem Ends.mono {s σ T T' Q Q'} (h : Ends lim P d s σ T Q) (hT : T ≤ T')
    (hQ : ∀ σ', Q σ' → Q' σ') : Ends lim P d s σ T' Q' := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc.trans hT, hQ _ hq⟩

/-- What is proved about a program holds for the program with more procedures appended. -/
theorem Ends.append {s σ T Q} (h : Ends lim P d s σ T Q) (R : Program) :
    Ends lim (P ++ R) d s σ T Q := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he.append R, hc, hq⟩

theorem Ends.skip {σ T} {Q : State → Prop} (h : Q σ) : Ends lim P d .skip σ T Q :=
  ⟨σ, 0, .skip, Nat.zero_le _, h⟩

theorem Ends.set {σ T x e} {Q : State → Prop} (hs : e.Safe lim σ) (hT : e.cost + 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (e.val σ) }) : Ends lim P d (.set x e) σ T Q :=
  ⟨_, _, .set hs, hT, h⟩

theorem Ends.store {σ T a e} {Q : State → Prop} (ha : a.Safe lim σ) (he : e.Safe lim σ)
    (hA : lim.Addr (a.val σ)) (hT : a.cost + e.cost + 1 ≤ T)
    (h : Q { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }) :
    Ends lim P d (.store a e) σ T Q :=
  ⟨_, _, .store ha he hA, hT, h⟩

theorem Ends.seq {σ T s₁ s₂} {Q : State → Prop} (T₁ T₂ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' T₂ Q) (hT : T₁ + T₂ ≤ T) :
    Ends lim P d (.seq s₁ s₂) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .seq he₁ he₂, by omega, hq⟩

theorem Ends.ite {σ T c s₁ s₂} {Q : State → Prop} (T' : ℕ) (hs : c.Safe lim σ)
    (h₁ : c.Holds σ → Ends lim P d s₁ σ T' Q) (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ T' Q)
    (hT : c.cost + 1 + T' ≤ T) : Ends lim P d (.ite c s₁ s₂) σ T Q := by
  by_cases hv : c.Holds σ
  · obtain ⟨σ', k, he, hk, hq⟩ := h₁ hv
    exact ⟨σ', _, .iteTrue hs hv he, by omega, hq⟩
  · obtain ⟨σ', k, he, hk, hq⟩ := h₂ hv
    exact ⟨σ', _, .iteFalse hs hv he, by omega, hq⟩













/-- Loops.  I i is the invariant before round number i (counted from 0) of n rounds, and b i bounds
the cost of that round. -/
theorem Ends.while {σ c s} {Q : State → Prop} (I : ℕ → State → Prop) (n : ℕ) (b : ℕ → ℕ)
    (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ (b i) (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ) :
    Ends lim P d (.while c s) σ (∑ i ∈ Finset.range n, (c.cost + 1 + b i) + (c.cost + 1)) Q := by
  have aux : ∀ j i σ, i + j = n → I i σ →
      Ends lim P d (.while c s) σ
        (∑ k ∈ Finset.range j, (c.cost + 1 + b (i + k)) + (c.cost + 1)) Q := by
    intro j
    induction j with
    | zero =>
      intro i σ hij hi
      obtain rfl : i = n := by omega
      obtain ⟨h1, h2, h3⟩ := hn σ hi
      exact ⟨σ, _, .whileFalse h1 h2, by simp, h3⟩
    | succ j ih =>
      intro i σ hij hi
      obtain ⟨h1, h2, σ', k₁, he₁, hk₁, hi'⟩ := hs i σ (by omega) hi
      obtain ⟨σ'', k₂, he₂, hk₂, hq⟩ := ih (i + 1) σ' (by omega) hi'
      refine ⟨σ'', _, .whileTrue h1 h2 he₁ he₂, ?_, hq⟩
      rw [Finset.sum_range_succ']
      have : ∀ k, i + 1 + k = i + (k + 1) := fun k => by omega
      simp only [this] at hk₂
      simp only [Nat.add_zero]
      omega
  simpa using aux n 0 σ (by omega) hI

/-- Loops in which every round costs at most b. -/
theorem Ends.whileConst {σ c s T} {Q : State → Prop} (I : ℕ → State → Prop) (n b : ℕ) (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ Ends lim P d s σ b (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + b) + (c.cost + 1) ≤ T) : Ends lim P d (.while c s) σ T Q :=
  (Ends.while I n (fun _ => b) hI hs hn).mono (by simpa using hT) fun _ h => h
































/-- Calls: verify the body from the frame made of the arguments. -/
theorem Ends.call {σ T p args x body} {Q : State → Prop} (T' : ℕ) (ha : ∀ e ∈ args, e.Safe lim σ)
    (hp : P[p]? = some body) (hd : d < lim.depth)
    (h : Ends lim P (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ T'
      fun σ' => Q ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) : Ends lim P d (.call p args x) σ T Q := by
  obtain ⟨σ', k, he, hk, hq⟩ := h
  exact ⟨_, _, .call ha hp hd he, by omega, hq⟩

/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/

























/-! ## Simplification -/

attribute [simp] Expr.val Expr.cost Expr.Safe Op.eval Cond.Holds Cond.cost Cond.Safe frame












/-- The natural number behind an address that is a sum of two natural numbers. -/
@[simp] theorem toNat_natCast_add_natCast (a b : ℕ) : ((a : ℤ) + (b : ℤ)).toNat = a + b := by
  rw [← Nat.cast_add, Int.toNat_natCast]

/-! ## The limits -/
























end Light

end
end

section


/-!
# Regions of the memory, and the cells that a step leaves alone

A region is given by its first address `a` and its number `n` of cells.  `Inside a n b` says that
the cell `b` lies in it, `Outside a n b` that it does not, and `Apart a n a' n'` that two regions do
not meet.  `InOrder top [(a, n), (a', n'), …]` says that the listed regions lie one behind the other
and end at or below `top`.  All of these abbreviate linear inequalities.

`SameOn K μ μ'` says that the memory `μ'` agrees with `μ` on every cell that satisfies `K`.  It is
the one notion of "these cells are unchanged": a routine promises `SameOn K μ μ'` for the cells
`K` that it leaves alone.  (It is `Set.EqOn μ' μ {b | K b}`, stated with a predicate: the conditions
`K b` that occur are linear inequalities between addresses and are used as such.)  The usual choices
of `K` have names.

* `SameOutside μ μ' a n`: all cells outside one region; `SameOutside2` and `SameOutside3`: all cells
  outside two or three regions.
* `Kept μ μ' fr`: all cells below the free pointer `fr`.
* `KeptBut μ μ' fr out len`: all cells below `fr` outside the region of an output.

## How a fact is carried from one memory to a later one

A predicate `X` about a memory has one lemma of the name `X.keep` and of the form

  `theorem X.keep (h : X μ …) (hs : SameOn K μ μ' := by light_keep) : X μ' …`

where `K` describes the cells that `X` reads; `Seg.keep` is the model.  The argument `hs` has a
default proof.  So `h.keep`, with no argument, stands for "`h` still holds in the memory that is
asked for here".  The default proof `light_keep` uses every hypothesis of the form `SameOn _ ν ν'`
in the context, that is, the promises of the steps that were taken since `h` was obtained, and the
inequalities in the context that say where the regions lie.  In the proofs a promise is named when
the step is taken, as `same₂` in `rintro _ μ₂ ⟨sY, same₂⟩`.

`wrote μ dst f j` is the memory `μ` after a loop has written `f 0`, …, `f (j - 1)` to the cells from
`dst`.
-/

@[expose] public section

namespace Light

/-! ## Regions -/


















/-! ## Memories that agree on some cells -/























variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}




theorem SameOn.refl : SameOn K μ μ := fun _ _ => rfl




/-- Fewer cells are kept. -/
theorem SameOn.mono (h : SameOn K μ μ') (hK : ∀ b, K' b → K b) : SameOn K' μ μ' :=
  fun b hb => h b (hK b hb)

/-- Two steps that keep different cells. -/
theorem SameOn.then (h₁ : SameOn K₁ μ μ') (h₂ : SameOn K₂ μ' μ'') (hK : ∀ b, K b → K₁ b ∧ K₂ b) :
    SameOn K μ μ'' :=
  fun b hb => (h₂ b (hK b hb).2).trans (h₁ b (hK b hb).1)

/-- Writing a cell that need not be kept. -/
theorem SameOn.write (h : SameOn K μ μ') (hb : ¬ K b) (x : ℤ) :
    SameOn K μ (Function.update μ' b x) := fun c hc => by
  rw [Function.update_of_ne (by rintro rfl; exact hb hc)]; exact h c hc

/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}





/-- Nothing has been written yet. -/
theorem wrote_zero : wrote μ dst f 0 = μ := by
  funext a
  unfold wrote
  rw [if_neg (by omega)]

/-- A cell that has been written. -/
theorem wrote_done {i : ℕ} (h : i < j) : wrote μ dst f j (dst + i) = f i := by
  unfold wrote
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

/-- A cell that has not been written (yet). -/
theorem wrote_rest {a : ℕ} (h : Outside dst j a) : wrote μ dst f j a = μ a := by
  unfold wrote
  rw [if_neg (by omega)]

/-- One more cell is written. -/
theorem wrote_succ : Function.update (wrote μ dst f j) (dst + j) (f j) = wrote μ dst f (j + 1) := by
  funext a
  by_cases h : a = dst + j
  · subst h
    rw [Function.update_self, wrote_done (Nat.lt_succ_self j)]
  · rw [Function.update_of_ne h]
    unfold wrote
    by_cases h' : dst ≤ a ∧ a < dst + j
    · rw [if_pos h', if_pos (by omega)]
    · rw [if_neg h', if_neg (by omega)]














/-! ## The tactics -/









































end Light

end
end

section


/-!
# Index arithmetic: a pair of numbers as one number

General facts about natural numbers. A matrix with rows of length `n` is kept as one list, row
after row: the entry in row `a` and column `b < n` has the index `a * n + b`. This file has

* the bounds on such an index (`Nat.mul_add_lt_mul`, `Nat.mul_add_le_mul`);
* the way back from the index to the pair (`Nat.mul_add_div_of_lt`, `Nat.mul_add_inj_of_lt`,
  `Nat.div_lt_of_lt_mul'`, `Nat.mod_lt_of_lt_mul`, `Nat.exists_eq_mul_add_of_lt_mul`,
  `Nat.eq_mul_succ_iff`);
* the pair of the next index (`Nat.succ_div_mod_of_lt`, `Nat.succ_div_mod_of_ne`,
  `Nat.succ_div_mod_of_eq`);
* residues seen as natural numbers (`Int.toNat_emod_lt`, `Int.natCast_toNat_emod`).
-/

public section

namespace Nat

/-! ## Bounds on an index -/





/-- Row `a < m` ends within the matrix: `a * n + b ≤ m * n` for `b ≤ n`, so also for `b = n`. -/
theorem mul_add_le_mul {a b m n : ℕ} (ha : a < m) (hb : b ≤ n) : a * n + b ≤ m * n :=
  calc a * n + b ≤ a * n + n := Nat.add_le_add_left hb _
    _ = (a + 1) * n := (Nat.succ_mul a n).symm
    _ ≤ m * n := Nat.mul_le_mul_right n ha

/-! ## From the index back to the pair

The column is `Nat.mul_add_mod_of_lt : c < b → (a * b + c) % b = c`. -/

































/-! ## The next index -/























end Nat

namespace Int

/-! ## Residues as natural numbers -/










end Int

end
end

section


/-!
# Lists: entries with a default, blocks, sums, counting, sorted lists

General facts about lists. Arrays are lists here, and entry `i` of a list is `l.getD i d`. The
sections:

* Entries with a default: `getD` of a list that was appended to, cut, tabulated, mapped or changed
  in one place.
* Blocks: `(List.range n).flatMap f` puts the blocks `f 0, …, f (n - 1)` one after the other. Where
  an entry of a block stands, for blocks of any lengths and for blocks of one length.
* Sums: partial sums, the triangle inequality, and the sum over a list that enumerates the image of
  a finite set.
* A running minimum.
* Counting: how often a value occurs among the first entries of a list, or among the values of a
  function on `Fin n`; the list of the `j < n` with a property.
* Sorted lists: what `dropWhile` and `takeWhile` leave of a strictly increasing list; first
  occurrences in a weakly increasing list.
* Two notions of this project: `AbsLe l U` says that all members of `l` have absolute value at most
  `U`, and `sumLists` is the entrywise sum of lists of one length.
-/

@[expose] public section

namespace List

variable {α β : Type*}

/-! ## Entries with a default -/

























































/-! ## Blocks one after the other -/











































































/-! ## Sums -/









































section

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]














end



































/-! ## A running minimum -/
























/-! ## Counting -/












































































/-! ## Sorted lists -/

section Sorted

variable [LinearOrder α]








































end Sorted

end List

namespace ThreeSumApsp

variable {α β : Type*}

/-! ## Lists of integers that are bounded in absolute value -/
















/-! ## The entrywise sum of lists -/






















end ThreeSumApsp

end
end

section


/-!
# Segments of the memory

Seg μ a l says that the cells a, a + 1, …, a + l.length - 1 of the memory μ hold the list l.
SegN is Seg for a list of natural numbers, MatAt for a matrix written row by row, VecAt for a vector
of indices.  The file has the lemmas for reading a cell of a segment, writing into it, writing
elsewhere, and for cutting and joining segments.  Each of the four predicates has its lemma `keep`,
which carries it to a later memory.
-/

@[expose] public section

namespace Light

open ThreeSumApsp







variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}












@[simp] theorem Seg.nil : Seg μ a [] := fun i h => absurd h (by simp)

/-- Reading a cell of a segment. -/
theorem Seg.get (h : Seg μ a l) {i : ℕ} (hi : i < l.length) : μ (a + i) = l[i] := h i hi









theorem seg_cons : Seg μ a (x :: l) ↔ μ a = x ∧ Seg μ (a + 1) l := by
  constructor
  · intro h
    refine ⟨by have h0 := h 0 (by simp); rwa [Nat.add_zero, List.getElem_cons_zero] at h0,
      fun i hi => ?_⟩
    have := h (i + 1) (by simpa using hi)
    simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => simpa using h0
    | succ i =>
      have := h i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem seg_append : Seg μ a (l₁ ++ l₂) ↔ Seg μ a l₁ ∧ Seg μ (a + l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [h i (by simp; omega), List.getElem_append_left hi]
    · have := h (l₁.length + i) (by simp; omega)
      rw [List.getElem_append_right (by omega)] at this
      simpa [Nat.add_assoc] using this
  · rintro ⟨h₁, h₂⟩ i hi
    by_cases hi₁ : i < l₁.length
    · rw [List.getElem_append_left hi₁, h₁ i hi₁]
    · have hi₂ : i - l₁.length < l₂.length := by simp at hi; omega
      rw [List.getElem_append_right (by omega), ← h₂ _ hi₂]
      congr 1
      omega









/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]
















/-- Writing outside a segment. -/
theorem Seg.update_out (h : Seg μ a l) (hb : b < a ∨ a + l.length ≤ b) (x : ℤ) :
    Seg (Function.update μ b x) a l :=
  h.congr fun i hi => Function.update_of_ne (by omega) _ _

/-- Writing just after a segment makes it longer. -/
theorem Seg.snoc (h : Seg μ a l) (x : ℤ) : Seg (Function.update μ (a + l.length) x) a (l ++ [x]) :=
  seg_append.2 ⟨h.update_out (Or.inr le_rfl) x, by simp [seg_cons]⟩

/-- A segment all of whose cells are kept. -/
theorem Seg.of_sameOn {K : ℕ → Prop} (h : Seg μ b l) (hs : SameOn K μ μ')
    (hK : ∀ i < l.length, K (b + i)) : Seg μ' b l := h.congr fun i hi => hs _ (hK i hi)

theorem SameOutside.refl : SameOutside μ μ a n := SameOn.refl



































































/-- A matrix stays where it is if its cells do not change. -/
theorem MatAt.congr {n k : ℕ} {A : Matrix (Fin n) (Fin k) ℤ} (h : MatAt μ a A)
    (he : ∀ b, a ≤ b → b < a + n * k → μ' b = μ b) : MatAt μ' a A := fun i j => by
  have := Nat.mul_add_lt_mul i.isLt j.isLt
  rw [he _ (by omega) (by omega)]
  exact h i j






/-- A matrix that lies below e is still there in a memory that agrees below e. -/
theorem MatAt.congr_below {n k e : ℕ} {A : Matrix (Fin n) (Fin k) ℤ} (h : MatAt μ a A)
    (hlow : ∀ x < e, μ' x = μ x) (hle : a + n * k ≤ e) : MatAt μ' a A :=
  h.congr fun b _ hb => hlow b (by omega)
















end Light

end
end

section


/-!
# Derived rules: time that is not typed, blocks, counting loops

The rules of this file spare the typing of step counts.  Ends.next gives the first statement its
time and the rest of the program what is left; Ends.setThen, Ends.storeThen and Ends.iteThen do the
same for one assignment, store or branch, and Ends.setLast, Ends.storeLast and Ends.iteLast treat
the last statement of a program.  `Ends.pieceThen` and `Ends.pieceLast` are the two forms for a
piece of the program that has a lemma of its own.  In every rule the main premises come first, then
the side conditions, and last the comparison of times.  The comparison has the default proof
`light_time`, safety conditions have the default proof `light_side`.

A block is a statement without loops and calls.  s.Runs lim σ R says that the block s runs safely
from σ and ends in a state that satisfies R; Ends.block turns this into a fact about time, with the
cost computed. Ends.whileBlock is the rule for a loop whose body is a block.

Stmt.for i hi body is the loop "for i = 0, …, hi - 1 do body".  The rule Ends.for owns the counter:
the safety of the test and of the increment and the number of steps of the loop are settled here,
once. Ends.forMem is the common case in which the body changes no local variable, so that the
invariant speaks about the memory only.  The three parts of every loop rule are called start, round
and done.  A loop rule is told a bound b on the steps of a round; for a round that is a block with
a name, say xRound, this is xRound.blockCost.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Blocks -/




































/-! ## The default proofs -/



































/-! ## Rules for blocks -/























theorem Ends.of_blockSafe : ∀ {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}, s.BlockSafe lim σ →
    s.blockCost ≤ T → Q (s.after σ) → Ends lim P d s σ T Q
  | .skip, _, _, _, _, _, h => Ends.skip h
  | .set _ _, _, _, _, hs, hT, h => Ends.set hs hT h
  | .store _ _, _, _, _, hs, hT, h => Ends.store hs.1 hs.2.1 hs.2.2 hT h
  | .seq s t, _, _, _, hs, hT, h =>
    Ends.seq s.blockCost t.blockCost
      (Ends.of_blockSafe hs.1 le_rfl (Ends.of_blockSafe hs.2 le_rfl h)) hT
  | .ite c s t, σ, _, _, hs, hT, h =>
    Ends.ite (max s.blockCost t.blockCost) hs.1
      (fun hc => Ends.of_blockSafe (hs.2.1 hc) (le_max_left _ _)
        (by simpa only [Stmt.after, if_pos hc] using h))
      (fun hc => Ends.of_blockSafe (hs.2.2 hc) (le_max_right _ _)
        (by simpa only [Stmt.after, if_neg hc] using h))
      hT
  | .while _ _, _, _, _, hs, _, _ => hs.elim
  | .call _ _ _, _, _, _, hs, _, _ => hs.elim

/-- **Blocks.**  A block that runs safely from σ ends within any T ≥ s.blockCost, in the state
s.after σ. -/
theorem Ends.block {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop} (h : s.Runs lim σ Q)
    (hT : s.blockCost ≤ T := by first
                                  |
                                    ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                      (first
                                        | omega
                                        | ((ring_nf); (omega))))
                                  | omega
                                  |
                                    (simp [] <;>
                                        first
                                        | omega
                                        | ((ring_nf); (omega)))) : Ends lim P d s σ T Q :=
  Ends.of_blockSafe h.1 hT h.2

/-! ## Sequencing: what is left of the time goes to the rest of the program -/

/-- The first statement gets T₁ steps, the rest of the program what is left of T. -/
theorem Ends.next {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop} (T₁ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' (T - T₁) Q)
    (hT : T₁ ≤ T := by first
                           |
                             ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                   List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                               (first
                                 | omega
                                 | ((ring_nf); (omega))))
                           | omega
                           |
                             (simp [] <;>
                                 first
                                 | omega
                                 | ((ring_nf); (omega)))) : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q :=
  Ends.seq T₁ (T - T₁) h (by omega)





/-- A `skip` may be put behind a statement. -/
theorem Ends.skipLast {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s .skip)) σ T Q) : Ends lim P d s σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂ =>
    cases he₂
    exact ⟨σ', _, he₁, by omega, hq⟩

/-- A program that is defined as a sequence may be treated as the sequence. -/
theorem Ends.seqSelf {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q) : Ends lim P d ((Light.Stmt.seq s₁ s₂)) σ T Q :=
  h












































/-- A branch at the end of the program: both sides get the steps that the test leaves. -/
theorem Ends.iteLast {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d s₁ σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d s₂ σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by (((try have := Light.Std.space_le (by assumption)));
                                ((try have := Light.Std.const_le (by assumption)));
                                (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))) (hT : c.cost + 1 ≤ T := by first
                                                                                                                        |
                                                                                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                                                                            (first
                                                                                                                              | omega
                                                                                                                              | ((ring_nf); (omega))))
                                                                                                                        | omega
                                                                                                                        |
                                                                                                                          (simp [] <;>
                                                                                                                              first
                                                                                                                              | omega
                                                                                                                              | ((ring_nf); (omega)))) :
    Ends lim P d (.ite c s₁ s₂) σ T Q :=
  Ends.ite _ hs h₁ h₂ (by omega)

























/-! ## Loops whose body is a block -/

/-- **Loops whose body is a block.**  I j is the invariant before round j of n rounds.  The time is
computed from body.blockCost. -/
theorem Ends.whileBlock {σ : State} {c : Cond} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n : ℕ) (start : I 0 σ)
    (round : ∀ (j : ℕ) (σ : State), j < n → I j σ →
      c.Safe lim σ ∧ c.Holds σ ∧ body.Runs lim σ (I (j + 1)))
    (done : ∀ σ : State, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + body.blockCost) + (c.cost + 1) ≤ T := by first
                                                                       |
                                                                         ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                               List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                           (first
                                                                             | omega
                                                                             | ((ring_nf); (omega))))
                                                                       | omega
                                                                       |
                                                                         (simp [] <;>
                                                                             first
                                                                             | omega
                                                                             | ((ring_nf); (omega)))) :
    Ends lim P d (.while c body) σ T Q :=
  Ends.whileConst I n body.blockCost start
    (fun j σ hj hI => ⟨(round j σ hj hI).1, (round j σ hj hI).2.1,
      Ends.block (round j σ hj hI).2.2 le_rfl⟩) done hT

/-! ## Counting loops -/





/-- **Counting loops.**  I j is the invariant before round j.  The bound hi has the value n
throughout, n fits in a word, and the body keeps the counter and takes at most b steps.  The rule
supplies σ.loc i = j; I 0 is asked of σ with 0 in the counter, and I (j + 1) of the state after the
increment. -/
theorem Ends.for {σ : State} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n b : ℕ)
    (start : I 0 { σ with loc := Function.update σ.loc i 0 })
    (round : ∀ (j : ℕ) (σ : State), j < n → σ.loc i = j → I j σ → Ends lim P d body σ b fun σ' =>
      σ'.loc i = j ∧ I (j + 1) { σ' with loc := Function.update σ'.loc i ((j : ℤ) + 1) })
    (done : ∀ σ : State, σ.loc i = n → I n σ → Q σ)
    (bound : ∀ (j : ℕ) (σ : State), j ≤ n → σ.loc i = j → I j σ → hi.Safe lim σ ∧ hi.val σ = n)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by first
                                                          |
                                                            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                              (first
                                                                | omega
                                                                | ((ring_nf); (omega))))
                                                          | omega
                                                          |
                                                            (simp [] <;>
                                                                first
                                                                | omega
                                                                | ((ring_nf); (omega)))) :
    Ends lim P d (Stmt.for i hi body) σ T Q := by
  have h0 : (0 : ℤ) ≤ lim.word := le_trans (Int.natCast_nonneg n) hn
  refine Ends.seq 2 (n * (hi.cost + b + 7) + hi.cost + 3)
    (Ends.set (by simpa using h0) (by simp) ?_) (by omega)
  refine Ends.whileConst (fun j σ => σ.loc i = j ∧ I j σ) n (b + 4) ⟨by simp, by simpa using start⟩
    ?_ ?_ (le_of_eq (by simp only [Cond.cost, Expr.cost]; ring))
  · rintro j σ hj ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound j σ hj.le hc hI
    refine ⟨⟨trivial, hs⟩, ?_, Ends.seq b 4 ((round j σ hj hc hI).mono le_rfl ?_) le_rfl⟩
    · change σ.loc i < hi.val σ
      rw [hc, hv]
      exact_mod_cast hj
    · rintro σ' ⟨hc', hI'⟩
      have hval : (((Light.Expr.op Light.Op.add) (v i) (k 1))).val σ' = (j : ℤ) + 1 := by simp [hc']
      have hj' : (j : ℤ) + 1 ≤ n := by exact_mod_cast hj
      refine Ends.set ⟨trivial, ?_, ?_⟩ (by simp) ⟨?_, ?_⟩
      · change ((1 : ℕ) : ℤ) ≤ lim.word
        push_cast
        omega
      · change |(((Light.Expr.op Light.Op.add) (v i) (k 1))).val σ'| ≤ lim.word
        rw [hval, abs_of_nonneg (by omega)]
        omega
      · simp [hc']
      · rw [hval]
        exact hI'
  · rintro σ ⟨hc, hI⟩
    obtain ⟨hs, hv⟩ := bound n σ le_rfl hc hI
    refine ⟨⟨trivial, hs⟩, ?_, done σ hc hI⟩
    change ¬ σ.loc i < hi.val σ
    rw [hc, hv]
    exact lt_irrefl _

/-- **Counting loops whose body changes no local variable.**  Before round j the local variables are
the given ones with j in the counter, and I j holds of the memory.  The bound hi has the value n
throughout, n fits in a word, and the body takes at most b steps. -/
theorem Ends.forMem {loc : ℕ → ℤ} {μ : ℕ → ℤ} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ}
    {Q : State → Prop} (I : ℕ → (ℕ → ℤ) → Prop) (n b : ℕ) (start : I 0 μ)
    (round : ∀ (j : ℕ) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body ⟨Function.update loc i j, μ'⟩ b fun σ' =>
        σ'.loc = Function.update loc i j ∧ I (j + 1) σ'.mem)
    (done : ∀ μ' : ℕ → ℤ, I n μ' → Q ⟨Function.update loc i n, μ'⟩)
    (bound : ∀ (j : ℕ) (μ' : ℕ → ℤ), j ≤ n → I j μ' →
      hi.Safe lim ⟨Function.update loc i j, μ'⟩ ∧ hi.val ⟨Function.update loc i j, μ'⟩ = n)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by first
                                                          |
                                                            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                              (first
                                                                | omega
                                                                | ((ring_nf); (omega))))
                                                          | omega
                                                          |
                                                            (simp [] <;>
                                                                first
                                                                | omega
                                                                | ((ring_nf); (omega)))) :
    Ends lim P d (Stmt.for i hi body) ⟨loc, μ⟩ T Q := by
  refine Ends.for (fun j σ => σ.loc = Function.update loc i j ∧ I j σ.mem) n b
    ⟨by simp, start⟩ ?_ ?_ ?_ hn hT
  · rintro j ⟨_, μ'⟩ hj - ⟨rfl, hI⟩
    refine (round j μ' hj hI).mono le_rfl ?_
    rintro ⟨_, μ''⟩ ⟨rfl, hI'⟩
    exact ⟨by simp, by simp, hI'⟩
  · rintro ⟨_, μ'⟩ - ⟨rfl, hI⟩
    exact done μ' hI
  · rintro j ⟨_, μ'⟩ hj - ⟨rfl, hI⟩
    exact bound j μ' hj hI

end Light

end
end

section


/-!
# Arrays in the memory

A routine assumes the same facts about each of its arrays: which list it holds, how long the list
is, and that it lies below some address `top`, from which on the routine writes: the free pointer,
the place of the result, the scratch space.  `ListAt μ a l N top` is the record of these three
facts, and `ArrayAt μ a l N U top` adds a bound `U` on the entries.  `IndexAt μ a l N p top` is the
record for a list of natural numbers below `p`.  What a routine assumes is then a record with one
field for each array.

* `ListAt.keep`, `ArrayAt.keep`: an array stays in place when its cells do not change.
* `ListAt.mono`, `ArrayAt.mono`: `top` and `U` may grow.
* `ListAt.read`, `ArrayAt.read`, `ArrayAt.abs_read_le`: what a cell holds, and how large it is.
* `ListAt.drop_take`, `ArrayAt.drop_take`: a piece of an array is an array.
* `IndexAt.keep`, `IndexAt.read`, `IndexAt.getD_lt`: the same for natural numbers.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}















namespace ListAt




















end ListAt

namespace ArrayAt



























end ArrayAt









namespace IndexAt

variable {l : List ℕ} {p : ℕ}






















end IndexAt

end Light

end
end

section


/-!
# Local variables as a list

In the proof of a procedure body the state is written out as ⟨frame [a, b, …], μ⟩: the list
holds the local variables 0, 1, …, and all further ones are 0.  An assignment to local x replaces
entry x of the list (setLocal).  The rules of this file treat one statement each.  They are told the
value that is assigned or stored, and they ask for one fact about each expression: that its
evaluation stays within the limits and gives this value (Expr.Gives).  This fact and the comparison
of the costs are proved by default from the hypotheses in the context.  Ends.forFrame and
Ends.forShape are the rules for counting loops in this form.  In the names of the rules, To says
that the state is ⟨frame l, μ⟩.

Locals by name, and locals whose values do not matter:

* `setLocals l [(x, a), (y, b), …]` is the list `l` after the assignments `x := a`, `y := b`, ….
  With the names of the locals for `x`, `y`, … it describes the locals of a procedure by name:
  `setLocals [] [(Size, n), (Bound, U), …]`.
* `updateLocals loc [(x, a), (y, b), …]` is the same for locals that are not given as a list.  A
  lemma about a piece of text that several procedures share is stated for arbitrary locals `loc`.
* `refreshLocals l loc xs` is the list `l` with the entries `xs` read from `loc`.
* `LocalsBut xs l loc` says that `loc` agrees with `frame l` except perhaps at the locals `xs`.  In
  an invariant, `xs` are the scratch variables.  `Ends.asFrame` goes from such locals to a list, and
  `LocalsBut.of_eq` comes back.
* `Ends.pieceTo` and `Ends.pieceToThen` use a lemma about a piece of text that assigns only the
  locals `xs`: afterwards the locals are `refreshLocals l loc' xs`, where `loc'` are the locals of
  which the lemma speaks.  The lemma need not mention the locals that the piece does not assign.
* `Ends.forScratch` is the rule for a counting loop whose body may change the scratch variables
  `xs`: the round says nothing about the locals.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The list of the locals -/









/-- Reading a local after an assignment. -/
theorem frame_setLocal : ∀ (l : List ℤ) (x : ℕ) (z : ℤ) (y : ℕ),
    frame (setLocal l x z) y = if y = x then z else frame l y
  | [], 0, z, 0 => by simp
  | [], 0, z, y + 1 => by simp
  | [], x + 1, z, 0 => by simp
  | [], x + 1, z, y + 1 => by simpa using frame_setLocal [] x z y
  | a :: l, 0, z, 0 => by simp
  | a :: l, 0, z, y + 1 => by simp
  | a :: l, x + 1, z, 0 => by simp
  | a :: l, x + 1, z, y + 1 => by simpa using frame_setLocal l x z y

/-- An assignment to a local, in terms of the list. -/
theorem update_frame_setLocal (l : List ℤ) (x : ℕ) (z : ℤ) :
    Function.update (frame l) x z = frame (setLocal l x z) := by
  funext y
  rw [frame_setLocal, Function.update_apply]



/-! ## The value of an expression -/





/-! ## One statement -/

section rules

variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}














/-- `x := e`, where e gives z. -/
theorem Ends.setTo {x : ℕ} {e : Expr} (z : ℤ) (h : Q ⟨frame (setLocal l x z), μ⟩)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by (((try have := Light.Std.space_le (by assumption)));
                                                  ((try have := Light.Std.const_le (by assumption)));
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : e.cost + 1 ≤ T := by first
                                 |
                                   ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                         List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                     (first
                                       | omega
                                       | ((ring_nf); (omega))))
                                 | omega
                                 |
                                   (simp [] <;>
                                       first
                                       | omega
                                       | ((ring_nf); (omega)))) :
    Ends lim P d (.set x e) ⟨frame l, μ⟩ T Q := by
  refine Ends.set he.1 hT ?_
  rw [he.2]
  simp only [update_frame_setLocal]
  exact h

/-- `x := e ; s`, where e gives z.  The rest s of the text gets the steps that are left. -/
theorem Ends.setToThen {x : ℕ} {e : Expr} {s : Stmt} (z : ℤ)
    (h : Ends lim P d s ⟨frame (setLocal l x z), μ⟩ (T - (e.cost + 1)) Q)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by (((try have := Light.Std.space_le (by assumption)));
                                                  ((try have := Light.Std.const_le (by assumption)));
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : e.cost + 1 ≤ T := by first
                                 |
                                   ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                         List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                     (first
                                       | omega
                                       | ((ring_nf); (omega))))
                                 | omega
                                 |
                                   (simp [] <;>
                                       first
                                       | omega
                                       | ((ring_nf); (omega)))) :
    Ends lim P d ((Light.Stmt.seq (.set x e) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.setTo z h he le_rfl) hT

/-- `mem[a] := e`, where a gives the address b, which lies in the memory, and e gives z. -/
theorem Ends.storeTo {a e : Expr} (b : ℕ) (z : ℤ) (h : Q ⟨frame l, Function.update μ b z⟩)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : a.cost + e.cost + 1 ≤ T := by first
                                          |
                                            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                              (first
                                                | omega
                                                | ((ring_nf); (omega))))
                                          | omega
                                          |
                                            (simp [] <;>
                                                first
                                                | omega
                                                | ((ring_nf); (omega)))) :
    Ends lim P d (.store a e) ⟨frame l, μ⟩ T Q := by
  obtain ⟨⟨ha, hav⟩, ⟨he, hev⟩, hb⟩ := he
  refine Ends.store ha he ?_ hT ?_
  · rw [hav]
    exact ⟨Int.natCast_nonneg b, by exact_mod_cast hb⟩
  · rw [hav, hev, Int.toNat_natCast]
    exact h

/-- `mem[a] := e ; s`, where a gives the address b, which lies in the memory, and e gives z. -/
theorem Ends.storeToThen {a e : Expr} {s : Stmt} (b : ℕ) (z : ℤ)
    (h : Ends lim P d s ⟨frame l, Function.update μ b z⟩ (T - (a.cost + e.cost + 1)) Q)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : a.cost + e.cost + 1 ≤ T := by first
                                          |
                                            ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                  List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                              (first
                                                | omega
                                                | ((ring_nf); (omega))))
                                          | omega
                                          |
                                            (simp [] <;>
                                                first
                                                | omega
                                                | ((ring_nf); (omega)))) :
    Ends lim P d ((Light.Stmt.seq (.store a e) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.storeTo b z h he le_rfl) hT

/-- **Counting loops whose body is a block that changes no local variable**, with the locals as a
list.  Before round j the locals are the given ones with j in the counter, and I j holds of the
memory.  The bound hi gives n, and n fits in a word.  The round is a goal about the body, for the
rules of this file, and its time is body.blockCost, so that no number is typed.  A loop or a call
counts 0 steps in blockCost; for a body that contains one use Ends.forShape. -/
theorem Ends.forFrame {i : ℕ} {hi : Expr} {body : Stmt} (I : ℕ → (ℕ → ℤ) → Prop) (n : ℕ)
    (start : I 0 μ)
    (round : ∀ (j : ℕ) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body ⟨frame (setLocal l i j), μ'⟩ body.blockCost fun σ' =>
        σ'.loc = frame (setLocal l i j) ∧ I (j + 1) σ'.mem)
    (done : ∀ μ' : ℕ → ℤ, I n μ' → Q ⟨frame (setLocal l i n), μ'⟩)
    (bound : ∀ (j : ℕ) (μ' : ℕ → ℤ), j ≤ n → I j μ' →
      hi.Gives lim ⟨frame (setLocal l i j), μ'⟩ n := by intros; (((try have := Light.Std.space_le (by assumption)));
                                                                       ((try have := Light.Std.const_le (by assumption)));
                                                                       (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + body.blockCost + 7) + hi.cost + 5 ≤ T := by first
                                                                       |
                                                                         ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                               List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                                           (first
                                                                             | omega
                                                                             | ((ring_nf); (omega))))
                                                                       | omega
                                                                       |
                                                                         (simp [] <;>
                                                                             first
                                                                             | omega
                                                                             | ((ring_nf); (omega)))) :
    Ends lim P d (Stmt.for i hi body) ⟨frame l, μ⟩ T Q := by
  refine Ends.forMem I n body.blockCost start ?_ ?_ ?_ hn hT
  · intro j μ' hj hI
    rw [update_frame_setLocal]
    exact round j μ' hj hI
  · intro μ' hI
    rw [update_frame_setLocal]
    exact done μ' hI
  · intro j μ' hj hI
    rw [update_frame_setLocal]
    exact bound j μ' hj hI


































end rules

/-! ## Locals by name, and locals whose values do not matter -/




































































section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}

























/-! ## A piece of program text with a lemma of its own -/

variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}































/-! ## Counting loops with scratch variables -/













































end

end Light

end
end

section


/-!
# Calls

Meets lim P p d vals μ T R is the specification of a procedure: procedure number p of the program P,
run at depth d on the arguments vals in the memory μ, ends within T steps with a result and a memory
that satisfy R. A routine is proved to meet such a specification (Meets.of_body), and a caller uses
the specification only, so that the proof of a caller does not depend on the body of a callee.

The specification of a routine x, as its callers assume it, has the form
`∀ (data) μ, hypotheses → ∀ d, d + k ≤ lim.depth → Meets lim P p d vals μ T R`.  Here k is the
number of levels of calls that x needs below itself, and d, the depth at which the body of x runs,
comes last.

There is one rule for calls, in four forms.  It is told the fact about the callee, from which it
reads the values of the arguments, the time and what holds afterwards, and it asks for what follows
the call.  Three side goals have default proofs: the arguments are safe and have these values, one
more level of calls is allowed, and the time suffices.  Ends.callTo and Ends.callToThen are the rule
for a state ⟨frame l, μ⟩; Ends.callLast and Ends.callThen are the same for local variables that are
not given as a list.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Specifications of procedures -/







section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}



















/-- A specification holds for the program with more procedures appended. -/
theorem Meets.append (h : Meets lim P p d vals μ T R) (P' : Program) :
    Meets lim (P ++ P') p d vals μ T R := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, getElem?_append_of_eq_some hp P', he.append P'⟩

end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : State → Prop} {s : Stmt}

/-- `x := p(args)`, where the arguments give vals.  The procedure runs at depth d + 1. -/
theorem Ends.callLast (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨Function.update loc x r, μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨loc, μ⟩) ∧ args.map (·.val ⟨loc, μ⟩) = vals := by (((try have := Light.Std.space_le (by assumption)));
                                                                                                        ((try have := Light.Std.const_le (by assumption)));
                                                                                                        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d (.call p args x) ⟨loc, μ⟩ T Q := by
  obtain ⟨body, hb, he⟩ := hp
  obtain ⟨hs, rfl⟩ := ha
  exact Ends.call T' hs hb hd (he.mono le_rfl fun _ hR => h _ _ hR) hT











/-- `x := p(args)`, with the local variables as a list.  The procedure runs at depth d + 1. -/
theorem Ends.callTo (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨frame (setLocal l x r), μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d (.call p args x) ⟨frame l, μ⟩ T Q :=
  Ends.callLast hp (fun r μ' hR => update_frame_setLocal l x r ▸ h r μ' hR) ha hd hT

/-- `x := p(args) ; s`, with the local variables as a list.  The procedure runs at depth d + 1. -/
theorem Ends.callToThen (hp : Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Ends lim P d s ⟨frame (setLocal l x r), μ'⟩
      (T - ((args.map Expr.cost).sum + 2 + T')) Q)
    (ha : (∀ e ∈ args, e.Safe lim ⟨frame l, μ⟩) ∧ args.map (·.val ⟨frame l, μ⟩) = vals := by
      (((try have := Light.Std.space_le (by assumption)));
        ((try have := Light.Std.const_le (by assumption)));
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d ((Light.Stmt.seq (.call p args x) s)) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.callTo hp h ha hd le_rfl) hT

end

end Light

end
end

section


/-!
# A polynomial bound in the parameters fits in a word

The running-time claims hold at every word size W ≥ b (log₂ p₁ + ⋯ + log₂ p_r + 1), where p₁, …, p_r
are the parameters of the instance and the slope b is chosen with the program (`Admissible`).  A
light program states its limits as a polynomial in the parameters,
`polyBound s k params` = 2^s ((p₁ + 1) ⋯ (p_r + 1))^k.

The main fact is `polyBound_le`: this bound is at most 2^W as soon as b ≥ s + k r + k.  Each factor
p + 1 is at most 2^(log₂ p + 1) (`prod_succ_le`), so with S the sum of the logarithms the bound is
at most 2^(s + k (S + r)), and s + k (S + r) ≤ (s + k r + k) (S + 1) ≤ W.
-/

@[expose] public section

namespace Light

open ThreeSumApsp.WordRam


































/-- The bound is positive. -/
theorem one_le_polyBound (s k : ℕ) (params : List ℕ) : 1 ≤ polyBound s k params := by
  have : 0 < (params.map (· + 1)).prod := List.prod_pos (by simp)
  exact Nat.mul_pos (by positivity) (by positivity)



































/-- A power of two times the bound is a bound of the same form. -/
theorem polyBound_mul (s s' k : ℕ) (params : List ℕ) :
    2 ^ s' * polyBound s k params = polyBound (s' + s) k params := by
  simp only [polyBound, pow_add, mul_assoc]









end Light

end
end

section


/-!
# Problems, solvers, and the interpretation of "is solved in time T" in the light language

A *task* is a problem together with a calling convention: which arguments a procedure gets, what the
memory holds when it is called, and what the result and the memory have to be when it returns.
`Solves task P p T need` says that procedure number `p` of the program `P` solves the task within
`T` steps, if the limits of the run allow for `need`.  A reduction of the paper is a *host*: a
procedure that calls an arbitrary solver of another task.

Conventions.

* A solver gets sizes, a bound `U` on the absolute values of the numbers, the addresses of its
  arrays, and as last argument the free pointer `fr`.  All inputs and outputs lie below `fr`.  The
  solver may write its output segments and any cell from `fr` on, and no other cell.  Nothing is
  assumed about the cells from `fr` on, so a solver can be called again and again.
* A solver has to be correct for every valid bound `U` that it is given.
* A solver is a pair of a program and a procedure number.  What is proved about it holds for every
  program that begins with this program, so a host appends its own procedures.

A `Task` is a problem whose time and need depend on a size and a bound.  `TaskN` and `SolvesN` are
the same notions with a list of parameters.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

/-! ## Limits -/
















/-- A smaller need is allowed for if a larger one is, also with a larger free pointer and at a
larger depth if the sums are not larger. -/
theorem Need.Ok.mono {r r' : Need} {lim : Limits} {fr fr' d d' : ℕ} (h : r.Ok lim fr d)
    (hw : r'.word ≤ r.word) (hc : fr' + r'.cells ≤ fr + r.cells)
    (hd : d' + r'.depth ≤ d + r.depth) : r'.Ok lim fr' d' :=
  ⟨le_trans (by exact_mod_cast hw) h.word, hc.trans h.cells, h.space, hd.trans h.depth⟩








/-! ## Specifications of single routines -/






/-! ## Tasks and solvers -/




















































/-! ## Hosts -/






















/-! ## Tasks with a list of parameters -/

























/-- A solver meets the specification of its task, at the depth d at which it runs. -/
theorem SolvesN.meets {task : TaskN} {P₀ : Program} {p : ℕ} {T₀ : List ℕ → ℕ}
    {need : List ℕ → Need} (h : SolvesN task P₀ p T₀ need) (R : Program) {lim : Limits} {d : ℕ}
    (x : task.Inst) {μ : ℕ → ℤ} {fr : ℕ} (hpre : task.Pre x μ fr)
    (hok : (need (task.pars x)).Ok lim fr d) :
    Meets lim (P₀ ++ R) p d (task.args x ++ [(fr : ℤ)]) μ (T₀ (task.pars x))
      (task.Post x μ fr) := by
  obtain ⟨body, hp, hb⟩ := h
  exact ⟨body, getElem?_append_of_eq_some hp R, hb R lim d x μ fr hpre hok⟩






end Light

end
end

section


/-!
# The answer of a decision problem as a number

A routine for a decision problem returns 1 for yes and 0 for no: `flag p` is this number for the
proposition `p`.
-/

@[expose] public section

namespace ThreeSumApsp

























end ThreeSumApsp

end
end

section


/-!
# Ceilings of quotients and logarithms, floors and ceilings of roots

General facts about natural and real numbers. The quotient of two natural numbers, rounded up, is
Mathlib's `a ⌈/⌉ b`. It is computed by `Nat.ceilDiv_eq_add_pred_div : a ⌈/⌉ b = (a + b - 1) / b`.
It is the ceiling of the real quotient (`Nat.ceil_div_eq_ceilDiv`) and the least `k` with
`a ≤ k * b` (`Nat.ceilDiv_le_iff`, `Nat.lt_ceilDiv_iff`), so `a ≤ a ⌈/⌉ b * b < a + b`
(`Nat.le_ceilDiv_mul`, `Nat.ceilDiv_mul_lt`). The power of `b` with exponent `⌈log_b n⌉` is at most
`b * n` (`Nat.pow_clog_le_mul`). A natural number is compared with an `e`-th root by its `e`-th
power (`Real.natCast_le_rpow_inv_iff`, `Real.rpow_inv_le_natCast_iff`). `cbrtCeil n` is the cube
root of `n`, rounded up.
-/

public section

namespace Nat

/-! ## The ceiling of a quotient of natural numbers -/






























/-! ## The ceiling of a logarithm

`Real.natCeil_logb_natCast : ⌈Real.logb b n⌉₊ = Nat.clog b n` passes from real to natural numbers,
and `Nat.le_pow_clog : 1 < b → x ≤ b ^ Nat.clog b x` is the lower bound. -/



end Nat

namespace Real

/-! ## Roots

The `e`-th root of `t` is written `(t : ℝ) ^ ((e : ℝ)⁻¹)`. With these two lemmas,
`Nat.le_floor_iff` and `Nat.ceil_le`, its floor and its ceiling are described by powers of natural
numbers. -/





end Real

namespace ThreeSumApsp




end ThreeSumApsp

end
end

section


/-!
# Logarithms and real powers

Small facts on `Real.log`, `Real.logb`, `Nat.clog`, `Real.sqrt` and real powers that the estimates
of the paper use silently.

* Values, in the namespace `Real` and named by Mathlib's convention: `1 / 2 < log 2 < 1`,
  `log 4 = 2 log 2`, `log 9 = 2 log 3`, `1 ≤ log 4`, `1 / 2 ≤ log x` for `x ≥ 2`, `1 ≤ log x` for
  `x ≥ 3`, `log₂ 7 < 2.81`, `4 ≤ √D` for `D ≥ 16`.
* The rounded logarithm: `⌈log_b n⌉ < log_b n + 1` (`Real.natCast_clog_lt_logb_add_one`),
  `c ^ ⌈log_b n⌉ ≤ c * n ^ (log_b c)` (`Real.pow_clog_le_mul_rpow_logb`).
* The definition `logU u = log (max u 2)`, the paper's `log U`.
-/

@[expose] public section

namespace Real

/-! ### Values -/

/-- `1 / 2 < log 2`. -/
theorem one_half_lt_log_two : 1 / 2 < log 2 :=
  lt_trans (by norm_num) log_two_gt_d9































/-! ### The rounded logarithm `Nat.clog` -/
















end Real

namespace ThreeSumApsp






end ThreeSumApsp

end
end

section


/-!
# Calculating with `O(n^a)` and `Õ(n^a)`

Closure properties of the two classes `IsBigOPow f a`, that is `f(n) = O(n^a)`, and
`IsPowPolylog f a`, that is `f(n) = O(n^a (log n)^{O(1)})`, which the paper writes `Õ(n^a)`.

A bound enters by `of_abs_le`, by `of_isBigO`, or from the model functions (`isBigOPow_rpow`,
`isBigOPow_natCast_pow`, `isBigOPow_const`, `isPowPolylog_rpow_mul_log_pow`, `isPowPolylog_log_pow`,
and for rounded powers `isBigOPow_ceil_rpow`, `isBigOPow_floor_rpow` and their inverses;
`IsBigOPow.natCeil` for rounding in general). Both classes are closed under sums, constant factors
and passing to a smaller function (`mono_left`). A product has the exponent `a + b` and a power the
exponent `a * k` (`pow`, `rpow`), to be brought to the wanted form by `mono`, which asks only for an
inequality between exponents. Substituting `n ↦ size n` multiplies nonnegative exponents
(`IsBigOPow.comp`, `IsPowPolylog.comp`), for `size n = O(n^μ)`, and then `log (size n) = Õ(1)`
(`IsBigOPow.isPowPolylog_log_natCast`). The classes are related by `IsBigOPow.isPowPolylog` and,
with a loss in the exponent, `IsPowPolylog.isBigOPow`; `eventually_abs_le` absorbs the constant as
well.
-/

public section

open Filter Asymptotics

namespace ThreeSumApsp

variable {f g : ℕ → ℝ} {a b : ℝ}

/-! ### `O(n^a)` -/











namespace IsBigOPow




































end IsBigOPow





























/-! ### `Õ(n^a)` -/



















namespace IsPowPolylog






























































end IsPowPolylog



















end ThreeSumApsp

end
end

section


/-!
# One-sided bounds `O(n^a)`, `Õ(n^a)` and `n^{a+o(1)}`

A running time is bounded from above only. `UpperBigOPow f a`, `UpperPowPolylog f a` and
`UpperPowLittleO f a` say that `f(n)` is eventually at most `C n^a`, at most `C n^a (log n)^e`, and
at most `n^{a+ε(n)}` with `ε(n) → 0`, where `IsBigOPow`, `IsPowPolylog` and `IsPowLittleO` say this
of `|f(n)|`.

A bound on `|f|` is a bound on `f` (`IsBigOPow.upperBigOPow`), and the function may be replaced by a
smaller one (`mono_left`); these two lemmas have the same names for the three classes. For `Õ(n^a)`
and `n^{a+o(1)}` a bound on `f` is a bound by a nonnegative function of the class that bounds `|f|`
(`UpperPowPolylog.exists_isPowPolylog`). For `Õ(n^a)` the closure properties follow: a bound on `f`
is a bound on `|f|` if `f` is eventually nonnegative (`UpperPowPolylog.isPowPolylog`), sums,
nonnegative constant factors, products with a nonnegative factor, a larger exponent (`mono`).
Logarithms and the `o(1)` are absorbed by a strictly larger exponent
(`UpperPowPolylog.upperBigOPow`, `UpperPowLittleO.upperBigOPow`).
-/

@[expose] public section

open Filter Asymptotics

namespace ThreeSumApsp















variable {f f' g : ℕ → ℝ} {a b : ℝ}

/-! ### `O(n^a)` from above -/








namespace UpperBigOPow






end UpperBigOPow

/-! ### `Õ(n^a)` from above -/



namespace UpperPowPolylog


















































end UpperPowPolylog

/-! ### `n^{a+o(1)}` from above -/






namespace UpperPowLittleO




















end UpperPowLittleO

end ThreeSumApsp

end
end

section


/-!
# Orders of growth of counts

The time and the need of a program are natural numbers, given by explicit expressions in the
parameters of the input.  Only their order of growth is needed.  This file has one calculus
that reads the order of growth off such an expression, so that no constant is ever written out.

A *scale* (`Scale α ι`) fixes the parameters `x : α` for which bounds are claimed (`dom`) and some
quantities that are at least 1 there: the *bases* `base i`, whose powers are counted, and one more,
`hidden`, whose powers are not.  `s.SoftO t e` says that the count `t` is at most a constant times a
power of `hidden` times the monomial `∏ i, base i ^ e i`.  Three examples:

* bases `n`, `√D`, `κ log n` and `hidden = 1`: `s.SoftO t ![2, 1, 1]` is `t = O(n² √D κ log n)`;
* one base `√n` and `hidden = log n`: `s.SoftO t ![3]` is `t = Õ(n^{3/2})`;
* no base and `hidden = n U`: `s.SoftO t ![]` says that `t` is polynomially bounded.

So `SoftO` is `O` up to powers of `hidden`: it is `O` itself if `hidden = 1`, and `Õ` if `hidden` is
a logarithm.  The bounds hold on the whole domain and not only from some point on.

The exponents follow the expression.  A constant has the exponents 0 (`SoftO.const`), a sum the
larger ones (`SoftO.add`), a product their sum (`SoftO.mul`), a power their multiple (`SoftO.pow`).
Exponents may be raised (`SoftO.mono`), and the count may be replaced by a smaller one
(`SoftO.of_le`, `SoftO.of_forall_le`).  If every base is at most `2 ^ hidden`, the binary logarithm
of a bounded count has the exponents 0 (`SoftO.log2`).

The tactic `growth [h₁, h₂, …]` applies these rules from the outside to the inside of the
expression.  The facts `hᵢ` bound the quantities at which the rules stop: parameters, and functions
whose bound is a lemma of its own.  A function that is to be followed into its definition is
unfolded first.

A bound leaves the calculus by `SoftO.exists_le`, or as a `Dominated` statement by
`SoftO.dominated`.
-/

@[expose] public section

namespace ThreeSumApsp














namespace Scale










variable {α ι : Type*} [Fintype ι] (s : Scale α ι)

















variable {s} {x : α} {e e' : ι → ℕ} {c c' : ℕ}







namespace SoftO

variable {t t₁ t₂ : α → ℕ} {e₁ e₂ : ι → ℕ}

/-! ### Entering and leaving -/













/-! ### The rules -/








































































end SoftO

end Scale








































end ThreeSumApsp

end
end

section


/-!
# Polynomially bounded needs

The need of a program is given by explicit expressions in the size n of the input and the bound U on
its numbers.  `PolyBounded F` says that F(n, U) is at most a polynomial in (n + 1)(U + 1).  It is
the calculus `ThreeSumApsp.Scale.SoftO` on the scale `polyScale`, and the tactic `growth_poly`
proves it by following the expression.

Three such functions make a polynomially bounded need (`PolyBounded.polyNeed`), and the need of a
solver that a host calls has three such parts (`PolyNeed.word`, `PolyNeed.cells`, `PolyNeed.depth`).
So the need of a host is polynomially bounded if the need of its solver is; the tactic `poly_need`
proves this from the definition of the need of the host.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

/-! ## Upper bounds that are polynomial in (n + 1)(U + 1) -/













namespace PolyBounded

variable {F : ℕ → ℕ → ℕ}









end PolyBounded






namespace PolyBounded





end PolyBounded

/-! ## The need of a solver that a host calls

A polynomially bounded need, at a size `A(n, U)` and a bound `B(n, U)` that are polynomially
bounded, has polynomially bounded parts. -/

namespace PolyNeed

variable {need : ℕ → ℕ → Need} {A B : ℕ × ℕ → ℕ} {a b : Fin 0 → ℕ}









end PolyNeed








end Light

end
end

section


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





/-! ## Thin instances: `n ≥ D^18` -/

/-- `D^{1+a} ≤ n` for `a ≤ 17`. -/
theorem mul_rpow_le_of_pow_le {n D : ℕ} {a : ℝ} (hD : 1 ≤ D) (hDn : D ^ 18 ≤ n) (ha : a ≤ 17) :
    (D : ℝ) * (D : ℝ) ^ a ≤ n := by
  have hD1 : (1 : ℝ) ≤ D := Nat.one_le_cast.2 hD
  calc (D : ℝ) * (D : ℝ) ^ a = (D : ℝ) ^ (1 + a) := by
        rw [Real.rpow_add (zero_lt_one.trans_le hD1), Real.rpow_one]
    _ ≤ (D : ℝ) ^ ((18 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1 (by push_cast; linarith)
    _ = ((D ^ 18 : ℕ) : ℝ) := by rw [Real.rpow_natCast, Nat.cast_pow]
    _ ≤ n := Nat.cast_le.2 hDn

/-- Writing the matrices: `n D ≤ n² / D^a`. -/
theorem mul_le_sq_div_rpow {n D : ℕ} {a : ℝ} (hD : 1 ≤ D) (hDn : D ^ 18 ≤ n) (ha : a ≤ 17) :
    (n : ℝ) * (D : ℝ) ≤ (n : ℝ) ^ 2 / (D : ℝ) ^ a := by
  rw [le_div_iff₀ (Real.rpow_pos_of_pos (Nat.cast_pos.2 hD) a), mul_assoc, sq]
  exact mul_le_mul_of_nonneg_left (mul_rpow_le_of_pow_le hD hDn ha) n.cast_nonneg

/-- `1 ≤ n² / D^a`. -/
theorem one_le_sq_div_rpow {n D : ℕ} {a : ℝ} (hD : 1 ≤ D) (hDn : D ^ 18 ≤ n) (ha : a ≤ 17) :
    1 ≤ (n : ℝ) ^ 2 / (D : ℝ) ^ a :=
  (one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.2 ((Nat.one_le_pow _ _ hD).trans hDn))
    (Nat.one_le_cast.2 hD)).trans (mul_le_sq_div_rpow hD hDn ha)

/-- `n² / √D ≤ n² / D^a` for `a ≤ 1/2`. -/
theorem sq_div_sqrt_le_sq_div_rpow (n : ℕ) {D : ℕ} {a : ℝ} (hD : 1 ≤ D) (ha : a ≤ 1 / 2) :
    (n : ℝ) ^ 2 / Real.sqrt D ≤ (n : ℝ) ^ 2 / (D : ℝ) ^ a := by
  rw [Real.sqrt_eq_rpow]
  exact div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos (Nat.cast_pos.2 hD) a)
    (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 hD) ha)
































/-! ## The pieces of Corollary 15 -/





























end ThreeSumApsp

end
end

section


/-!
# Logarithms up to a constant factor

Bounds on logarithms in the calculus `Dominated`, for every argument of a domain and not only for
large ones.

* Absorbing logarithms, for `x ≥ 1`: `(log x + 1) ^ e` is `O(x ^ η)` for `η > 0`
  (`dominated_log_add_one_pow_rpow`), hence `x ^ a * (log x) ^ e = O(x ^ b)` for `a < b`
  (`dominated_rpow_mul_log_pow_rpow`).
* From 2 on: `log x + 1 = O(log x)` (`dominated_log_add_one_log`) and `⌈log_b n⌉ + 1 = O(log n)`
  (`dominated_clog_add_one_log`).

For a natural number or a field of a parameter record in place of `x`, use `Dominated.comp`.
-/

public section

namespace ThreeSumApsp

open Real

/-! ### Absorbing logarithms, for all `x ≥ 1` -/




































/-! ### `log x + 1` and `⌈log_b n⌉ + 1` are `O(log)`, from `2` on -/





end ThreeSumApsp

end
end

section


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

















/-! ## `logU` of a multiple -/





/-! ## `logU` along bounds that are polynomial in `n` -/





end ThreeSumApsp

end
end

section


/-!
# The steps and the scratch space of Strassen's recursion

At level j the operands are 2^j × 2^j matrices whose entries are vectors of p numbers, so that an
operand has 4^j · p numbers.  strScr p j ≤ 4^j · p (`strScr_le`), and both strScr and strSteps are
monotone in p.
-/

public section

namespace Light.Sec3




























end Light.Sec3

end
end

section


/-!
# The parameters of Theorems 17 and 19 in integer arithmetic

The proof of Theorem 19 chooses `D` and `g` as rounded real powers of `n`: "Let D be the largest
power of four with D ≤ n^{1/18}, […] and let g := ⌈D^{1/36}⌉" on the route through Theorem 5, and
"Let D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉" on the route through Corollary 26.  The reduction of
Theorem 17 cuts each residue class into chunks of at most `n²/√D` query pairs and splits `C` into
pieces of at most `⌈s/g⌉` vertices, where `s = ⌊√D⌋`.  A program finds all these numbers by
operations on natural numbers.

* `rootFloor e t` is `⌊t^{1/e}⌋` and `rootCeil e t` is `⌈t^{1/e}⌉` (`floor_rpow_inv`,
  `ceil_rpow_inv`); they are characterised by `x ≤ rootFloor e t ↔ x^e ≤ t` (`le_rootFloor_iff`) and
  `rootCeil e t ≤ g ↔ t ≤ g^e` (`rootCeil_le_iff`).
* The four functions `paramD₅Nat`, `paramG₅Nat`, `paramD₂₆Nat`, `paramG₂₆Nat` are the parameters
  of the proof of Theorem 19 (`paramD₅Nat_eq`, `paramG₅Nat_eq`, `paramD₂₆Nat_eq`, `paramG₂₆Nat_eq`);
  they are at least 1 and at most `n` or `D` (`paramD₂₆Nat_le`, `paramG₅Nat_le`, `paramG₂₆Nat_le`).
* The sizes of the proof of Theorem 17: `⌊n²/√D⌋ = ⌊√(n⁴/D)⌋` (`queryCapNat_eq`), `s` is the integer
  square root (`sOf_eq_sqrt`), and the rounded quotients are `a ⌈/⌉ b` (`pieceSizeNat_eq`,
  `numPiecesNat_eq`, `numChunks_eq`).  The middle part `C_k × ℤ_p` of an instance has at most `D`
  vertices (`pieceSize_mul_le`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Roots, rounded down and up -/























/-! ## The parameters of the proof of Theorem 19 -/
































































/-! ## The sizes of the instances of the proof of Theorem 17 -/







































































end ThreeSumApsp.Spec

end
end

section


/-!
# Scanning a piece (the proof of Theorem 17)

"For every query pair that the oracle accepts, scan the piece C_k of its instance for a c with
S(a,b,c) = 0".  The procedure scan (`scanBody`) goes through an interval of vertices `c` for a fixed
pair `(a, b)` (`scan_spec`, `scan_meets`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}






/-! ## The three arrays of weights -/










/-! ## Scanning an interval of vertices -/

namespace Scan


















end Scan





























end Light.Sec3

end
end

section


/-!
# The parameters of Theorems 17 and 19, without division and without roots

The proof of Theorem 19 chooses D as "the largest power of four with D ≤ n^{1/18}"
and g := ⌈D^{1/36}⌉, or D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉; the reduction of Theorem 17 uses
⌊n²/√D⌋ and quotients rounded up.  The language has neither division nor roots, so all of these are
found by counting up.  A power is compared with a bound without forming a number above the bound
times the base.

* powLt(g, e, t), for g ≥ 1, returns 1 if g^e < t, and 0 if not (`powLt_meets`); what it holds after
  i factors is `capPow g t i`.
* rootCeil(e, t) returns the least g with g^e ≥ t (`rootCeil_meets`).
* The four parameters; 5 and 26 stand for the two routes of Theorem 19, through Theorem 5 and
  through Corollary 26.  d5(n) returns the largest power of four that is at most n^{1/18}, g5(D)
  returns ⌈D^{1/36}⌉, d26(n) returns ⌊n^{1/18}⌋, and g26(D) returns ⌈D^{0.0315}⌉; g5 and g26
  are for D ≥ 1 (`d5_spec`, `g5_spec`, `d26_spec`, `g26_spec`).
* queryCapNat(n, D) returns ⌊n²/√D⌋, and ceilDiv(a, b) returns ⌈a/b⌉ (`queryCapNat_meets`,
  `ceilDiv_meets`).

No routine touches the memory.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Comparing a power with a bound -/













namespace PowLt









end PowLt













/-! ## Roots, rounded up -/

namespace RootCeil







end RootCeil


















/-! ## The four parameters of the proof of Theorem 19 -/
















































































































/-! ## ⌊n²/√D⌋ and quotients rounded up -/












































































































end Light.Sec3

end
end

section


/-!
# Brute force (the proof of Theorem 19)

In the proof of Theorem 19, "smaller instances are solved by brute force": the procedure brute
(`bruteBody`) scans all of `C` for every pair `(a, b)` (`brute_spec`, `brute_meets`).  It takes at
most `100 n³ + 100` steps (`brute_solves`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}















namespace Brute














end Brute
























section

variable {pScan : ℕ} {μ : ℕ → ℤ} {ab bc ac n a U fr : ℕ} {AB BC AC : List ℤ}





end















end Light.Sec3

end
end

section


/-!
# The host of Theorem 17: the need stays polynomial

The need of a procedure says what it asks of the limits of a run: the largest number that it forms,
the cells that it uses, and the depth of its calls.  If the need of the solver is polynomially
bounded (`PolyNeedN`), then so is the need of the host (`hostNeed_poly`: `PolyNeed` of `hostNeed`).
The need of the host is an explicit expression in `n`, `U`, `D`, `g` and a few quantities derived
from them.  Each of these is at most a polynomial in `(n + 1)(U + 1)` (`PolyBounded`), and such
bounds are closed under sums, products and powers.

* The quantities: `⌊√D⌋ ≤ D`, the number of binary digits of `U` is at most `U`,
  `2^{len + 1} ≤ 4(U + 1)`, `2^⌈log₂ n⌉ ≤ 2(n + 1)`, `⌊n²/√D⌋ ≤ n²`, `⌈s/g⌉ ≤ s + g` with
  `s = ⌊√D⌋`.
* The numbers (`polyBounded_hostWord`), the cells (`polyBounded_chooseCells`,
  `polyBounded_hostLayout`), and each of the three parts of the need of the solver on the instances
  of the host (`polyBounded_sup`).  The depth adds `O(⌈log₂ n⌉)` calls (`polyBounded_clog`).
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

namespace HostPoly

/-! ## The quantities -/

















variable {D g : ℕ → ℕ}



/-! ## The numbers, the cells, and the solver -/

section parts

variable (hD : PolyBounded fun n _ => D n)
include hD









end parts

end HostPoly



end Light.Sec3

end
end

section


/-!
# The host of Theorem 17: the program, assembled

The procedures of the host are appended to a program `P₀` that already holds a solver of
Lop-AE-SparseTri and the two procedures that compute the parameters `D` and `g`.  This file has the
list of the procedures (`et17Procs`), their numbers (`et17NumsAt`), the proof that the program so
obtained is the context that the top procedure assumes (`et17Ctx_assembled`), and the
result: the host solves Exact Triangle (`et17_solves`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec




































































                                              -- 28

variable {P₀ : Program} {pS pD pG : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
  {Dfun Gfun tD tG wD wG : ℕ → ℕ}





end Light.Sec3

end
end

section


/-!
# Theorem 17 as a claim about programs of the light language

`Claim.Theorem_17 M MM D g` says: from every solver of Lop-AE-SparseTri with running time `T` there
is a solver of Exact Triangle whose running time is at most
`4ng (T + C n²/√D) + C (κ n³ log n/g + MM(n) D^{3/2} + n² D g)` (`bound17`, with the three terms
`termScans`, `termPrime`, `termBuild` of the additional time).  Here `κ` is the exponent in
`|w(e)| ≤ n^κ` (the paper's ν), `D` and `g` are the parameters of the reduction as functions of
`n`, `MM(n)` is the number of ring operations of the matrix multiplication, and `M` says what
"solved in time" means.
This file reduces the claim, for the interpretation by programs of the light language, to two facts
about a host: it turns solvers into solvers and keeps their need (word size, cells, depth of calls)
polynomial, and its time function obeys the bound (`ObeysBound17`, `claim17_of_host`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp


















end Light.Sec3

end
end

section


/-!
# Theorem 17: the time of each routine, up to a constant

The running time of the reduction of Theorem 17 is a sum of the time functions of its routines.  The
theorem bounds the additional time by "O(ν n³ log n/g + n^{ω+o(1)} D^{3/2} + n² D g)", where ν is
the exponent in `|w(e)| ≤ n^ν`; it is `κ` below.  The form for programs, `Claim.Theorem_17`, has,
here, Strassen's exponent `log₂ 7` in the second term.  This file bounds each
routine by a monomial in `n`, `√D` and `κ log n`, uniformly in `n`, `D`, `g`, `U` and `κ` under the
hypotheses of the theorem, and says which monomials are within which of the three terms.  No
constant is computed.

* `Steps t B` says that the number `t` of steps is `O(B)`, uniformly in the parameters.  Such bounds
  can be added and multiplied, and they absorb constant factors.
* Every time function is a polynomial in a few quantities, and each of these is at most a monomial
  `mon a b c = n^a (√D)^b (κ log n)^c`: `⌊√D⌋`, `g` and the size `⌈s/g⌉` of a piece are at most
  `√D`; `2^⌈log₂ n⌉ ≤ 2n`; the number of binary digits of `U ≤ n^κ` is `O(κ log n)` (section "The
  basic quantities").  So a routine takes `O(mon a b c)` steps (`StepsMon t a b c`), and the
  exponents are read off its time function, in the calculus `Scale.SoftO` on the scale `costScale`.
* All three bases are at least 1.  So a monomial is within the first term if its exponents are at
  most `(2, 1, 1)`, within the second if they are at most `(2, 3, 0)`, within the third if they are
  at most `(2, 2, 0)` (`Scale.SoftO.withinScans`, `Scale.SoftO.withinPrime`,
  `Scale.SoftO.withinBuild`).
* The choice of the prime runs through at most `√D` primes (`steps_chooseTime`).  The product of the
  two matrices is within the second term, as in the paper: Strassen's recursion makes
  `7^⌈log₂ n⌉ = O(n^{log₂ 7})` products of polynomials of degree below `p ≤ √D`
  (`steps_sqrt_mul_strSteps`).  The residues of the weights, computed bit by bit for each prime,
  take `O(√D n² κ log n)` steps, which is within the first term.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The hypotheses -/































namespace CostParams.Hyp

variable {θ : CostParams} (h : θ.Hyp)
include h












































end CostParams.Hyp

/-! ## Numbers of steps up to a constant -/






namespace Steps

variable {t t₁ t₂ : CostParams → ℕ} {B B₁ B₂ : CostParams → ℝ}

























end Steps

/-! ## Monomials -/



















/-! ## The basic quantities -/

























































/-! ## The routines -/














































































/-! ## The three terms of the bound dominate the monomials -/






























































section within

variable {t : CostParams → ℕ} {e : Fin 3 → ℕ}















end within

namespace Steps

variable {t₁ t₂ m : CostParams → ℕ} {B : CostParams → ℝ}






end Steps

/-! ## The choice of the prime -/







































































end Light.Sec3

end
end

section


/-!
# Theorem 17 for programs of the light language, with the two choices of parameters of Section 3.3

Theorem 17 reduces Exact Triangle to at most `4ng` instances of Lop-AE-SparseTri(n, D). As
a claim about programs: from every solver of Lop-AE-SparseTri there is a solver of Exact Triangle
whose time obeys the bound of the theorem, here with Strassen's algorithm for the matrix product
(`Claim.Theorem_17` with `strassen`).  The program is the host `et17`.

The host takes the procedures that compute `D` from `n` and `g` from `D` as parameters.  Here they
are the routines for the two choices of the proof of Theorem 19: "Let D be the largest power of four
with D ≤ n^{1/18} [...] and let g := ⌈D^{1/36}⌉", and "Let D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉".
The program is the solver's program, followed by the parameter routines (`paramProcs`), followed by
the procedures of the host.

1. The four routines are parameter procedures in the sense of the host (`paramProc_d5`,
   `paramProc_g5`, `paramProc_d26`, `paramProc_g26`).
2. The parameters and the numbers that the routines form are polynomially bounded
   (`polyBounded_paramD₅Nat`, `polyBounded_paramG₅Nat`, `polyBounded_wD5`, `polyBounded_wG5`,
   and the same for the second choice).  So the need of the host (word size, cells, depth of calls)
   is polynomially bounded if that of the solver is (`hostNeed_poly`).  With `et17_solves` this
   makes the host turn solvers into solvers (`host_of_paramProcs`).
3. The routines take `O(n)`, respectively `O(D)`, steps (`steps_tD5`, `steps_tG5`, `steps_tD26`,
   `steps_tG26`).  So the time of the host obeys the bound of the theorem (`obeysBound17_hostTime`).
   Together: `claim_theorem_17₅` and `claim_theorem_17₂₆`.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The parameter routines -/











































/-! ## The parameters and the words are polynomially bounded -/




































/-! ## The time of the parameter routines -/



















/-! ## The host with parameter routines -/















end Light.Sec3

end
end

section


/-!
# The running time of brute force (the proof of Theorem 19)

The `100 n³ + 100` steps of brute are within the form `C n³ (1 + log u)` in which the running times
for Exact Triangle with weights of absolute value at most `u` are stated (`claim_bruteForce`).
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec



end Light.Sec3

end
end

section


/-!
# Two programs in one: relocation of procedures

A program grows by appending procedures.  To put two programs, each with its own numbering of
procedures, into one, the second is placed behind the first (`Program.behind`), and the numbers of
the procedures that it calls are shifted by the length of the first (`Stmt.shift`).

A run of a statement in P is then a run of the shifted statement, with the same states and the
same number of steps (`Exec.shift`, an induction on the run in which only the case of a call has
anything to do: `Program.getElem?_behind_right`).  So everything proved with `Ends` carries over
(`Ends.shift`, `Ends.shift_append`).
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}






















end Light

end
end

section


/-!
# Two algorithms for Exact Triangle and a threshold on the number of vertices

For every threshold n₀ there is a constant C₀ such that, if Exact Triangle is solved in time T₁ and
in time T₂, then it is solved in time T₁ + C₀ for n < n₀ and T₂ + C₀ for n ≥ n₀.  This is
`Closure.ChooseBySize`, with "Exact Triangle is solved in time T" read as `SolvedIn etTask T`
(`closure_chooseBySize`).  It is used in the proof of Theorem 19, where the bounds hold
for large n only.

Two solvers are put into one program, the second behind the first (`solves_behind`), and one more
procedure looks at the number of vertices and calls the first solver below a fixed threshold n₀ and
the second one from the threshold on (`bySize_spec`).  The need stays polynomial
(`polyNeed_bySize`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}


















namespace ChooseHost







end ChooseHost

open ChooseHost



end Light.Sec3

end
end

section


/-!
# Corollary 15: counting triangles with the thin matrix product, and detecting with counting

Two steps of the proof of Corollary 15, with "the problem is solved in time T" read as
`ThinSolvedIn` and `LopSolvedIn`.

* `Claim.LopCountFromThinProduct`: "Apply Theorem 5 with N = n to the two biadjacency matrices".  An
  instance of #Lop-AE-SparseTri is given by its two biadjacency matrices, so a solver of the thin
  matrix product is a solver of #Lop-AE-SparseTri as it stands, called with U = 1, where U, the
  fourth argument and parameter, is the bound on the entries of the matrices
  (`solvesN_count_of_thin`, `claim_lopCountFromThinProduct`).
* `Claim.LopDetectFromCount`: the counts "are nonzero exactly for the query pairs that lie in a
  triangle".  One more procedure calls the counting solver and replaces every nonzero count by 1
  (`detect_spec`, `claim_lopDetectFromCount`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

namespace LopHosts

/-! ## Bounds -/

/-- One more parameter with the value 1 costs a factor `2^e`. -/
theorem polyBound_snoc_one (s e : ℕ) (ps : List ℕ) :
    polyBound s e (ps ++ [1]) = polyBound (s + e) e ps := by
  simp only [polyBound, List.map_append, List.map_cons, List.map_nil, List.prod_append,
    List.prod_cons, List.prod_nil, mul_one,
    mul_pow, pow_add]
  norm_num
  ring

/-- Twice the bound leaves room for one more. -/
theorem polyBound_le_succ (s e : ℕ) (ps : List ℕ) :
    polyBound s e ps + 1 ≤ polyBound (1 + s) e ps := by
  have h1 := one_le_polyBound s e ps
  rw [← polyBound_mul]
  omega

/-! ## Counting with the thin matrix product -/

/-- A solver of the thin matrix product solves #Lop-AE-SparseTri. -/
theorem solvesN_count_of_thin {P : Program} {p : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    (h : SolvesN thinTask P p Tn need) :
    SolvesN lopCountTask P p (fun ps => Tn (ps ++ [1])) fun ps => need (ps ++ [1]) := by
  obtain ⟨body, hp, hb⟩ := h
  refine ⟨body, hp, fun R lim d x μ fr hpre hok => ?_⟩
  obtain ⟨h1, -, h3⟩ := hpre
  have hpars : thinTask.pars x = lopCountTask.pars x ++ [1] := by
    simp only [thinTask, lopCountTask, List.cons_append, List.nil_append]
    rw [h3]
  have hrun := hb R lim d x μ fr h1 (hpars ▸ hok)
  rwa [hpars] at hrun

/-- A polynomially bounded need stays so when a parameter is fixed to 1. -/
theorem polyNeedN_snoc_one {need : List ℕ → Need} (h : PolyNeedN need) :
    PolyNeedN fun ps => need (ps ++ [1]) := by
  obtain ⟨s, e, h⟩ := h
  refine ⟨s + e, e, fun ps => ?_⟩
  rw [← polyBound_snoc_one]
  exact h _

end LopHosts

open LopHosts

/-- **Counting common neighbours is a thin matrix product** (Section 3.1). -/
theorem claim_lopCountFromThinProduct : Claim.LopCountFromThinProduct lightModel := by
  refine ⟨0, fun T hT => ?_⟩
  obtain ⟨P, p, Tn, need, hneed, hsol, htime⟩ := hT
  refine ⟨P, p, _, _, polyNeedN_snoc_one hneed, solvesN_count_of_thin hsol,
    fun n D w w' hn hD hw => ?_⟩
  have := htime n D w w' 1 1 hn hD le_rfl hw (by norm_num)
  simpa using this

/-! ## Detecting with counting -/

namespace LopArgs














end LopArgs
















namespace LopHosts

/-- There is one answer for each wanted position. -/
theorem length_thinOut (N D : ℕ) (X Y : List ℤ) {WI WJ : List ℕ} {w : ℕ} (h1 : WI.length = w)
    (h2 : WJ.length = w) : (thinOut N D X Y WI WJ).length = w := by
  simp [thinOut, h1, h2]

/-- **detect** solves Lop-AE-SparseTri. -/
theorem detect_spec {P₀ R : Program} {p : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    (hsol : SolvesN lopCountTask P₀ p Tn need) {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : lopDetectTask.Pre x μ fr)
    (hok : (lopDetectNeed need (lopDetectTask.pars x)).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (lopDetectBody p) ⟨frame (lopDetectTask.args x ++ [(fr : ℤ)]), μ⟩
      (lopDetectTime Tn (lopDetectTask.pars x))
      fun σ' => lopDetectTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hw := hok.space
  have hcells := hok.cells
  have hdep : d + ((need [x.N, x.D, x.w]).depth + 1) ≤ lim.depth := hok.depth
  have bO := hpre.1.belowOut
  have hlen := length_thinOut x.N x.D x.X x.Y hpre.1.lenWI hpre.1.lenWJ
  have hm : Meets lim (P₀ ++ R) p (d + 1)
      [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ (Tn [x.N, x.D, x.w]) fun _ μ₁ =>
        Seg μ₁ x.out (thinOut x.N x.D x.X x.Y x.WI x.WJ) ∧ KeptBut μ μ₁ fr x.out x.w :=
    hsol.meets R x hpre (hok.mono le_rfl le_rfl (by
      change d + 1 + (need [x.N, x.D, x.w]).depth ≤ d + ((need [x.N, x.D, x.w]).depth + 1)
      omega))
  change Ends lim (P₀ ++ R) d (lopDetectBody p)
    ⟨frame [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr], μ⟩
    (Tn [x.N, x.D, x.w] + 20 * x.w + 18) _
  -- the counts
  refine Ends.callToThen hm fun r μ₁ ⟨hseg, hk⟩ => ?_
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℤ, ∀ i, f i = if μ₁ (x.out + i) = 0 then 0 else 1 := ⟨_, fun _ => rfl⟩
  -- for i < w: the first i counts have been replaced
  refine Ends.forFrame (fun j μ' => μ' = wrote μ₁ x.out f j) x.w wrote_zero.symm ?round ?done
    (hT := by simp; omega)
  case round =>
    rintro j _ hj rfl
    have hread : wrote μ₁ x.out f j (x.out + j) = μ₁ (x.out + j) := wrote_rest (by omega)
    rw [← wrote_succ]
    -- if out[i] ≠ 0 then out[i] := 1
    refine Ends.iteLast (fun hc => Ends.skip ⟨rfl, ?_⟩) fun hc =>
      Ends.storeTo (x.out + j) 1 ⟨rfl, ?_⟩
    · have hc : μ₁ (x.out + j) = 0 := by simpa [hread] using hc
      have e : f j = wrote μ₁ x.out f j (x.out + j) := by rw [hf, if_pos hc, hread, hc]
      rw [e, Function.update_eq_self]
    · have hc : μ₁ (x.out + j) ≠ 0 := by simpa [hread] using hc
      rw [hf, if_neg hc]
  case done =>
    rintro _ rfl
    refine ⟨fun i hi => ?_, fun a ha => (wrote_rest ha.2).trans (hk a ha)⟩
    have hi' : i < x.w := by simpa [hlen] using hi
    rw [List.getElem_map, ← hseg i (by omega), ← hf]
    exact wrote_done hi'

/-- The need of detect is polynomially bounded if that of the counting solver is. -/
theorem polyNeedN_detect {need : List ℕ → Need} (h : PolyNeedN need) :
    PolyNeedN (lopDetectNeed need) := by
  obtain ⟨s, e, h⟩ := h
  refine ⟨1 + s, e, fun ps => ?_⟩
  have h1 := polyBound_le_succ s e ps
  obtain ⟨a, b, c⟩ := h ps
  simp only [lopDetectNeed]
  omega

end LopHosts

open LopHosts

/-- **Detection from counting** (proof of Corollary 15). -/
theorem claim_lopDetectFromCount : Claim.LopDetectFromCount lightModel := by
  refine ⟨20, fun T hT => ?_⟩
  obtain ⟨P, p, Tn, need, hneed, hsol, htime⟩ := hT
  refine ⟨P ++ [lopDetectBody p], P.length, lopDetectTime Tn, lopDetectNeed need,
    polyNeedN_detect hneed, ?_, fun n D w w' hn hD hw => ?_⟩
  · refine ⟨lopDetectBody p, by simp, fun R lim d x μ fr hpre hok => ?_⟩
    rw [List.append_assoc]
    exact detect_spec hsol hpre hok
  · have h1 := htime n D w w' hn hD hw
    have h2 : (w : ℝ) ≤ w' := by exact_mod_cast hw
    simp only [lopDetectTime, List.getD_cons_succ, List.getD_cons_zero]
    push_cast
    linarith

end Light.Sec3

end
end

section


/-!
# Tables of powers

powTable(dst, L, b) writes 1, b, b², …, b^(L-1) into the L cells from dst and changes nothing else,
within `powTableTime L` steps (`powTable_meets`).  The list of these powers is `powList b L`.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}




@[simp] theorem length_powList (b L : ℕ) : (powList b L).length = L := by simp [powList]





namespace PowTable









end PowTable

open PowTable




































































end Light

end
end

section


/-!
# Theorem 5 in the light language: sizes and places

The sizes of the tables and arrays of Theorem 5's program, and their places in the memory. No
program occurs here.

The program for Theorem 5 (the solver) and the data structure of Section 4 begin with the same
stage, the shared stage, which fills the shared block: a directory of 32 cells with the sizes and
the addresses of the areas (`dirList`), then the tables, then the encodings of all bands, then two
scratch areas. The solver has a private block behind it. The areas lie one after the other:
`Par.places` (the shared block) and `Par.places5` (the private block) say where every area begins
and ends. `Par.sizes` collects the inequalities between the sizes, each of which has a name of its
own.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## Sizes -/











namespace Par






















/-! ## The shared block, from its base address `b0` on -/











































end Par








/-! ## The private block of Theorem 5

The solver receives `N`, `D`, the number `w` of wanted positions, a bound `U` on the entries, the
addresses of `X`, `Y` (row by row), of the rows `WI` and the columns `WJ` of the wanted positions
and of the output, and as last argument the free pointer `fr`. All inputs and the output lie below
`fr`. The solver may write the output and the cells from `fr` on, and nothing is assumed about these
cells: a routine clears what it needs cleared. The shared block starts at `fr`, the private block
follows it. -/

namespace Par




























end Par

/-! ## The places and the sizes, as equations and inequalities -/

/-- The places of the shared block: each area begins where the one before it ends. -/
theorem Par.places (p : Par) (b0 : ℕ) :
    p.aDIR b0 = b0 ∧ p.aP3 b0 = b0 + 32 ∧ p.aP4 b0 = p.aP3 b0 + (p.L + 1)
      ∧ p.aP7 b0 = p.aP4 b0 + (p.L + 1)
      ∧ p.aP10 b0 = p.aP7 b0 + (p.L + 1) ∧ p.aPAS b0 = p.aP10 b0 + (p.L + 1)
      ∧ p.aPHI b0 = p.aPAS b0 + (p.L + 2) ∧ p.aPSI b0 = p.aPHI b0 + 70
      ∧ p.aMASK b0 = p.aPSI b0 + 70 ∧ p.aBAND b0 = p.aMASK b0 + p.KK * p.L
      ∧ p.aBLOCK b0 = p.aBAND b0 + p.N ∧ p.aDIG3 b0 = p.aBLOCK b0 + p.N
      ∧ p.aDIG4 b0 = p.aDIG3 b0 + p.N * p.Lo ∧ p.aENCA b0 = p.aDIG4 b0 + p.D * p.m
      ∧ p.aENCB b0 = p.aENCA b0 + p.nB * p.T ∧ p.aARR b0 = p.aENCB b0 + p.nB * p.T
      ∧ p.aZS b0 = p.aARR b0 + p.S7 ∧ p.sharedEnd b0 = p.aZS b0 + p.S7 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

namespace Par
variable (p : Par)





























end Par











end Light.Sec2

end
end

section


/-!
# The alphabets of Schönhage's identity as digits

Section 2.2 names seven left variables, seven right variables, ten output variables and
ten terms; Section 2.3.1 indexes arrays by strings over these alphabets.  Here every
letter gets a digit, so that a string becomes a number (`codeStr`).

* The left variables `x₁ x₂ x₃ p₁₁ p₁₂ p₂₁ p₂₂` are the digits `0, …, 6`; likewise the right
  variables.
* The output variables `z₁₁ z₁₂ … z₃₃ z₀` are the digits `0, …, 9`, and the terms `P₁₁ … P₃₃ P₀`
  likewise, so that `z_ij` and `P_ij` have the same digit `3(i-1) + (j-1)`, and `z₀` and `P₀` have
  the digit 9.
* Left and right strings are numbers in base 7 (`codeL`, `codeR`), output strings, vertices and
  leaves in base 10 (`codeO`, `codeT`), strings of indices of outer variables in base 3
  (`codeOuter`) and of inner variables in base 4 (`codeInner`), always with level 1 most
  significant.
* Which output variables are inner, and which term contributes to which output variable (Section
  2.2), is read off the digits (`outVar_isInner_iff`, `contributes_iff`).
* The coefficients of the linear forms `φ_λ` and `ψ_λ` (Section 2.2) are written out as the rows of
  two 10 × 7 tables, `phiTable` and `psiTable`, which the programs store row after row
  (`phiFlat_spec`, `psiFlat_spec`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Digits -/





























































































/-! Applying one of the five bijections gives the digit. -/











/-! ## Codes of strings -/

























/-! ### Codes of output strings and of vertices

The general facts about `codeStr`, under names of their own for the two codes that occur most. -/




































/-! ## The structure of the identity, in digits -/

































/-! ## The coefficients of the linear forms, as tables -/





















/-- The table of the `φ_λ(s)` has 70 entries. -/
@[simp] theorem length_phiFlat : phiFlat.length = 70 := rfl

/-- The table of the `ψ_λ(t)` has 70 entries. -/
@[simp] theorem length_psiFlat : psiFlat.length = 70 := rfl













end ThreeSumApsp.Spec

end
end

section


/-!
# Arrays on strings as lists

Section 2.3.1: "An array a on the left strings of length L assigns an integer a[u] to each u that is
a left string of length L."  In a program such an array is a list: an array on the strings of length
`n` over an alphabet of `b` letters is the list of its `b^n` entries in the order of the codes
(`arrStr`), so the entry at a string is the entry of the list at the code of the string
(`getD_arrStr`), and an entry of the list is 0 if the array is 0 at the string with that code
(`getD_arrStr_eq_zero`).  The arrays on left strings, on right strings and on leaves are the cases
`arrL`, `arrR` and `arrT`.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Arrays on the strings over any numbered alphabet -/

section
variable {α : Type} {b : ℕ} (e : α ≃ Fin b) [NeZero b] {n : ℕ} (a : (Fin n → α) → ℤ)






/-- The list has `b^n` entries. -/
theorem length_arrStr : (arrStr e a).length = b ^ n := by
  simp [arrStr]



















end

/-! ## The three kinds of arrays of Section 2 that the programs store -/


















/-- The list of an array on the leaves has `10^n` entries. -/
theorem length_arrT {n : ℕ} (enc : Leaf n → ℤ) : (arrT enc).length = 10 ^ n :=
  length_arrStr termEquiv enc















end ThreeSumApsp.Spec

end
end

section


/-!
# The memory map of Theorem 5: what depends on which cells

SharedReady.dirs lists the cells of the directory that the solver reads. SharedTables are the tables
of the shared block without the directory and the encodings; they depend only on the cells between
these two (SharedTables.congr), and all that the shared stage leaves behind depends only on the
cells of the shared block, without the last of the 32 cells of the directory, which the shared stage
does not use (SharedReady.congr, SharedReady.of_agree).
-/

public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## The directory -/

variable {p : Par} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ}
  {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}























/-! ## Only the shared block matters -/

/-- The tables lie between the directory and the encodings: they are still there in a memory that
agrees on these cells. -/
theorem SharedTables.congr {p : Par} {b0 : ℕ} {μ μ' : ℕ → ℤ} (h : SharedTables p b0 μ)
    (he : ∀ x, p.aP3 b0 ≤ x → x < p.aENCA b0 → μ' x = μ x) : SharedTables p b0 μ' := by
  have hplaces := p.places b0
  have lp : ∀ b, (powList b (p.L + 1)).length = p.L + 1 := fun b => length_powList b _
  have lphi := Spec.length_phiFlat
  have lpsi := Spec.length_psiFlat
  refine
    { p3 := h.p3.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      p4 := h.p4.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      p7 := h.p7.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      p10 := h.p10.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      phi := h.phi.congr fun i hi => he _ (by omega) (by omega)
      psi := h.psi.congr fun i hi => he _ (by omega) (by omega)
      mask := fun s hs => (h.mask s hs).congr fun i hi => he _ (by omega) ?_
      band := fun I hI => (he _ (by omega) (by omega)).trans (h.band I hI)
      block := fun I hI => (he _ (by omega) (by omega)).trans (h.block I hI)
      dig3 := fun I hI => (h.dig3 I hI).congr fun i hi => he _ (by omega) ?_
      dig4 := fun x hx => (h.dig4 x hx).congr fun i hi => he _ (by omega) ?_ }
  · rw [List.length_map, Spec.length_unrank] at hi
    have := Nat.mul_add_lt_mul hs hi
    omega
  · have := Nat.mul_add_lt_mul hI (show i < p.Lo by simpa [ThreeSumApsp.digitList] using hi)
    omega
  · have := Nat.mul_add_lt_mul hx (show i < p.m by simpa [ThreeSumApsp.digitList] using hi)
    omega

/-- What the shared stage leaves behind is kept by a memory that agrees on the cells of the shared
block, but for cell 31 of the directory, which the shared stage does not use. -/
theorem SharedReady.congr (h : SharedReady p hmL aX aY b0 X Y μ)
    (hag : ∀ a, b0 ≤ a → a < p.sharedEnd b0 → a ≠ b0 + 31 → μ' a = μ a) :
    SharedReady p hmL aX aY b0 X Y μ' := by
  have hplaces := p.places b0
  have tb : SharedTables p b0 μ' :=
    h.toSharedTables.congr fun x hlo hx => hag x (by omega) (by omega) (by omega)
  have henc : ∀ {a β i : ℕ}, p.aENCA b0 ≤ a → a + p.nB * p.T ≤ p.sharedEnd b0 → β < p.nB →
      i < p.T → μ' (a + β * p.T + i) = μ (a + β * p.T + i) := fun ha hend hβ hi => by
    have := Nat.mul_add_lt_mul hβ hi
    exact hag _ (by omega) (by omega) (by omega)
  refine
    { tb with
      dir := h.dir.congr fun i hi => ?_
      encA := fun β hβ => (h.encA β hβ).congr fun i hi =>
        henc le_rfl (by omega) hβ (by rwa [Spec.length_arrT] at hi)
      encB := fun β hβ => (h.encB β hβ).congr fun i hi =>
        henc (by omega) (by omega) hβ (by rwa [Spec.length_arrT] at hi) }
  simp only [dirList, List.length_map, List.length_cons, List.length_nil] at hi
  simp only [Par.aDIR]
  exact hag _ (by omega) (by omega) (by omega)








end Light.Sec2

end
end

section


/-!
# Theorem 30 in the light language: the memory map and the invariant of the data structure

The data structure occupies one block of the memory, from a base address b0 on. First comes the
shared block of Section 2 (directory, tables, the encodings of all bands), and behind it the areas
of Section 4:

    WD (L) | CUR (L) | BOX (L) | SS (m) | FP (1) | ROOTS (nB²) | TR (cap)

WD holds the digits of the output string of a query; CUR, BOX and SS are scratch strings; FP holds
the length of the trie array; ROOTS holds the roots of the tries, that of tile (β, β') in the cell
β nB + β'; TR is the trie area. Cell 31 of the directory holds t. `Areas` says where the tables that
the routines of Section 4 read and the areas of Section 4 lie, and `areas` proves it.

Two routines know this map: preCore(L, m, t, N, D, aX, aY, b0) builds the block from the matrices at
aX and aY, which lie below b0, and queryAt(I, J, b0) answers a query from it. They are relocatable,
so that Theorem 30, its offline form and Corollary 26 use the same two routines. The main procedures
of Theorem 30's programs only read the sizes from the input and compute the addresses. For Corollary
26 a routine of its own stands in between: it finds m and, from the threshold of the proof on, L and
t, writes padded copies of the matrices, and runs `preCore` on them.

Section 4.3: "Our data structure consists of three components: the list of the K₀² subsets Q
assigned to the block products of a tile […], the encodings of all row bands and all column bands,
and for every tile, the values of all its boxes". In the invariant DSReady the field shared holds
the first two, and the fields roots and trie hold the third: "for each tile we store its boxes, with
their values, in a standard trie on their strings of L symbols". The tries of all tiles lie in one
array (trie), and the table roots has the root of the trie of each tile. The invariant depends only
on the cells from b0 on, without the scratch strings (`DSReady.congr`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The map -/






















/-! ## Where the areas lie -/



















/-- The tables and the areas lie as Areas says. -/
theorem areas (p : Sec2.Par) (t b0 : ℕ) : Areas p t b0 := by
  have hplaces := p.places b0
  have hWD : aWD p b0 = p.sharedEnd b0 := rfl
  have hCUR : aCUR p b0 = aWD p b0 + p.L := rfl
  have hBOX : aBOX p b0 = aCUR p b0 + p.L := rfl
  have hSS : aSS p b0 = aBOX p b0 + p.L := rfl
  have hFP : aFP p b0 = aSS p b0 + p.m := rfl
  have hROOTS : aROOTS p b0 = aFP p b0 + 1 := rfl
  have hTR : aTR p b0 = aROOTS p b0 + p.nB * p.nB := rfl
  have hTOP : top p t b0 = aTR p b0 + trieCap p t + 1 := rfl
  constructor <;> omega










/-- The block holds more than its directory. -/
theorem base_add_lt_top (p : Sec2.Par) (t b0 : ℕ) : b0 + 32 < top p t b0 := by
  obtain ⟨⟩ := areas p t b0
  omega

/-- The block is not empty. -/
theorem base_lt_top (p : Sec2.Par) (t b0 : ℕ) : b0 < top p t b0 :=
  (Nat.le_add_right b0 32).trans_lt (base_add_lt_top p t b0)




/-- The scratch strings of a query lie in the block. -/
theorem scratch_in_block (p : Sec2.Par) (t b0 : ℕ) :
    b0 ≤ aWD p b0 ∧ aWD p b0 + (3 * p.L + p.m) ≤ top p t b0 := by
  obtain ⟨⟩ := areas p t b0
  omega

/-! ## The directory -/

namespace Dir




















end Dir

/-! ## The invariant -/



























section

variable {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}

/-- The invariant depends only on the cells from b0 on, without the scratch strings WD, CUR, BOX,
SS. -/
theorem DSReady.congr (h : DSReady p t hmL aX aY b0 X Y μ)
    (he : ∀ a, b0 ≤ a → Outside (aWD p b0) (3 * p.L + p.m) a → μ' a = μ a) :
    DSReady p t hmL aX aY b0 X Y μ' := by
  have hend : p.sharedEnd b0 = aWD p b0 := rfl
  obtain ⟨⟩ := areas p t b0
  exact ⟨h.shared.congr fun a ha hlt _ => he a ha (by omega),
    by rw [he _ (by omega) (by omega)]; exact h.cellT,
    h.roots.congr fun i _ => he _ (by omega) (by omega),
    h.trie.congr fun i _ => he _ (by omega) (by omega)⟩







/-- The invariant of the data structure only depends on the cells from b0 on. -/
theorem dsReady_congr (h : DSReady p t hmL aX aY b0 X Y μ) (he : ∀ a, b0 ≤ a → μ' a = μ a) :
    DSReady p t hmL aX aY b0 X Y μ' :=
  h.congr fun a ha _ => he a ha

end












/-! ## The two routines that know the map -/




































end Light.Sec4

end
end

section


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
















/-- Proof of Corollary 26, "Setting up": "pad the inner dimension to 4^m < 4D with zero columns of X
and zero rows of Y. This changes no entry of XY". -/
theorem Corollary26.padding {N D₀ : ℕ} (D' : ℕ) (hD : D₀ ≤ D') (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ) :
    padInnerCols D' X * padInnerRows D' Y = X * Y := by
  ext I J
  rw [Matrix.mul_apply, Matrix.mul_apply]
  -- The sum over the `D'` columns has the `D₀` terms of `XY`, and zeros at the added columns.
  refine (Fintype.sum_of_injective (Fin.castLE hD) (Fin.castLE_injective hD) _ _
    (fun k hk => ?_) fun k => ?_).symm
  · have hk' : ¬ (k : ℕ) < D₀ := fun h => hk ⟨⟨k, h⟩, rfl⟩
    simp only [padInnerCols, dif_neg hk', zero_mul]
  · simp only [padInnerCols, padInnerRows, Fin.val_castLE, k.isLt, dite_true, Fin.eta]











































































/-! ### Queries -/









































/-! ### Encodings -/






























/-! ### Conclusion -/























end ThreeSumApsp

end
end

section


/-!
# Corollaries 26 and 31 in the light language: m, the places of the padded matrices, the query

m = ⌈log₄ D⌉ (`logFour`), the places of the padded matrices and of the block of Theorem 30 behind
the free pointer (`paddedXAt`, `paddedYAt`, `blockAt`), the text of the query, and the bounds on the
entries of the padded matrices. The text of the query serves all rational parameters; its
specification is `QuerySpec31`, proved in `query31_meets`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Parameters and map -/









/-! ## The query -/

namespace Query31










end Query31








theorem abs_padInnerCols_le {N D₀ D' : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ} {U : ℤ}
    (h : ∀ i j, |X i j| ≤ U) (hU : 0 ≤ U) (i : Fin N) (j : Fin D') :
    |padInnerCols D' X i j| ≤ U := by
  unfold padInnerCols
  split_ifs
  · exact h _ _
  · simpa using hU

theorem abs_padInnerRows_le {N D₀ D' : ℕ} {Y : Matrix (Fin D₀) (Fin N) ℤ} {U : ℤ}
    (h : ∀ i j, |Y i j| ≤ U) (hU : 0 ≤ U) (i : Fin D') (j : Fin N) :
    |padInnerRows D' Y i j| ≤ U := by
  unfold padInnerRows
  split_ifs
  · exact h _ _
  · simpa using hU

theorem le_D_logFour (D₀ : ℕ) : D₀ ≤ D (logFour D₀) := Nat.le_pow_clog (by norm_num) D₀
















end Light.Sec4

end
end

section


/-!
# Corollaries 26 and 31 in the light language: rational parameters in the program text

Proof of Corollary 26: "Setting up. Let m := ⌈log₄ D⌉, and pad the inner dimension to 4^m < 4D";
proof of Corollary 31: "with L := ⌈cm⌉ and t := ⌈θm⌉". A program is a finite text, so it can hold c
and θ only if they are rational: c = a/b and θ = p/q (`RatParams`). For real c and θ the statements
follow by approximation (`exists_ratParams`). Corollary 26 is the case c = 21, θ = 1/9, with the
threshold 60 (`ratParams26`).

This file has the parameters, what a structure at the free pointer fr consists of (`structEnd`,
`Ready31`), what the routines ask of the limits (`Lim31`), the query with its specification and its
proof (`QuerySpec31`, `query31_meets`), and the text and the specification of the preprocessing
(`pre31Body`, `PreSpec31`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Parameters -/
















variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}















/-- t ≤ m. -/
theorem RatParams.t_le (G : RatParams) (m : ℕ) : G.t m ≤ m := by
  unfold RatParams.t
  have hq := G.hq
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  have h1 : 10 * G.p * m ≤ 9 * G.q * m := Nat.mul_le_mul_right _ G.hθ.le
  have h2 : G.p * m ≤ G.q * m := by
    have e1 : 10 * G.p * m = 10 * (G.p * m) := by ring
    have e2 : 9 * G.q * m = 9 * (G.q * m) := by ring
    omega
  omega





































/-- Below the threshold a structure has three cells. -/
theorem structEnd_small (h : logFour D₀ < G.m₀) (N fr : ℕ) : structEnd G N D₀ fr = fr + 3 :=
  if_pos h

/-- For m ≥ m₀ a structure ends with the block of Theorem 30. -/
theorem structEnd_large (h : G.m₀ ≤ logFour D₀) (N fr : ℕ) :
    structEnd G N D₀ fr = G.blockEnd N D₀ fr :=
  if_neg (not_lt.2 h)

/-- The block of Theorem 30 begins after the first three cells. -/
theorem add_three_le_blockAt (N D₀ fr : ℕ) : fr + 3 ≤ blockAt N D₀ fr := by
  unfold blockAt
  omega

/-- The block of Theorem 30 is not empty. -/
theorem RatParams.blockAt_lt_blockEnd (G : RatParams) (N D₀ fr : ℕ) :
    blockAt N D₀ fr < G.blockEnd N D₀ fr :=
  base_lt_top _ _ _

/-- The cells that a query of Theorem 30 writes lie in the block. -/
theorem RatParams.scratch_in_block (G : RatParams) (N D₀ fr : ℕ) :
    blockAt N D₀ fr ≤ aWD (parOf G N D₀) (blockAt N D₀ fr) ∧
      aWD (parOf G N D₀) (blockAt N D₀ fr) + (3 * (parOf G N D₀).L + (parOf G N D₀).m)
        ≤ G.blockEnd N D₀ fr :=
  Sec4.scratch_in_block _ _ _

/-- A structure has at least three cells. -/
theorem add_three_le_structEnd (G : RatParams) (N D₀ fr : ℕ) : fr + 3 ≤ structEnd G N D₀ fr := by
  have hblock := add_three_le_blockAt N D₀ fr
  have hend := G.blockAt_lt_blockEnd N D₀ fr
  by_cases h : logFour D₀ < G.m₀
  · rw [structEnd_small h]
  · rw [structEnd_large (not_lt.1 h)]
    omega
























































theorem Input31.zero_le_U (h : Input31 lim G X Y aX aY fr U) : 0 ≤ U :=
  le_trans (abs_nonneg _) (h.absX ⟨0, h.one_le_N⟩ ⟨0, h.one_le_D⟩)

/-! ## The query: the text is query31Body -/
















/-- A query to the data structure of Theorem 30 changes only cells of its block, so that the
structure stays ready. -/
theorem Ready31.of_query (h : Ready31 G X Y aX aY fr μ) (bX : aX + N * D₀ ≤ fr)
    (bY : aY + D₀ * N ≤ fr) (hm : G.m₀ ≤ logFour D₀) (hkept : ∀ a < blockAt N D₀ fr, μ' a = μ a)
    (hDS : Built31 G X Y fr μ') : Ready31 G X Y aX aY fr μ' := by
  have hb0 := add_three_le_blockAt N D₀ fr
  obtain ⟨hflag, hbase, -⟩ := h.large hm
  exact ⟨h.matX.congr_below hkept (by omega), h.matY.congr_below hkept (by omega),
    fun hm' => absurd hm (by omega),
    fun _ => ⟨(hkept _ (by omega)).trans hflag, (hkept _ (by omega)).trans hbase, hDS⟩⟩

/-- query31 reads the flag and calls the query of Theorem 30 if it is 1 and the inner product
otherwise; it returns the entry (XY)[I, J] and keeps the structure ready. -/
theorem query31_meets (G : RatParams) (hP : P[Proc.query31]? = some query31Body)
    (hq : QueryAtSpec lim P) (hip : IpAtSpec lim P) : QuerySpec31 lim P G := by
  intro N D₀ aX aY fr X Y U μ I J hin hR
  have hlim := hin.lim
  have bX := hin.belowX
  have bY := hin.belowY
  refine fun d hd => ⟨query31Body, hP, ?_⟩
  have hw := hlim.std.space_le
  have h100 := hlim.std.const_le
  have hU0 := hin.zero_le_U
  have hfr3 := add_three_le_structEnd G N D₀ fr
  have hsp := hlim.space
  unfold query31Body
  -- if mem[fr] = 1
  refine Ends.iteLast (fun hflag => ?_) (fun hflag => ?_) (hT := by simp [tQuery31])
  · -- the data structure has been built: return queryAt(I, J, mem[fr + 1])
    have hlarge : G.m₀ ≤ logFour D₀ := by
      by_contra hc
      have hzero := hR.small (by omega)
      have hone : μ fr = 1 := by simpa using hflag
      omega
    obtain ⟨-, hbase, hDS⟩ := hR.large hlarge
    have haddr : ((fr : ℤ) + 1).toNat = fr + 1 := by omega
    refine Ends.callTo
      (hq (parOf G N D₀) (switchOf31 G D₀) (logFour_le_levels G N D₀) (paddedXAt fr)
        (paddedYAt N D₀ fr) (blockAt N D₀ fr) _ _ U μ I J (G.t_le _) (hlim.large hlarge)
        (abs_padInnerCols_le hin.absX hU0) (abs_padInnerRows_le hin.absY hU0) hDS _ (by omega)) ?_
      (by (((try have := Light.Std.space_le (by assumption)));
            ((try have := Light.Std.const_le (by assumption)));
            (simp [Light.Limits.Addr, abs_le, -abs_mul, haddr, hbase] <;> omega)))
      (hT := by simp [tQuery31, if_neg (not_lt.mpr hlarge), parOf]; omega)
    rintro r μ' ⟨hr, hDS', hout⟩
    have hscratch := G.scratch_in_block N D₀ fr
    have hb0 := add_three_le_blockAt N D₀ fr
    have htop := structEnd_large hlarge N fr
    refine ⟨?_, hR.of_query bX bY hlarge (fun a ha => hout a (by omega)) hDS',
      fun a ha => hout a (by omega)⟩
    -- padding changes no entry of the product
    exact hr.trans (congrFun (congrFun
      (Corollary26.padding (D (logFour D₀)) (le_D_logFour D₀) X Y) I) J)
  · -- m is below the threshold: return the inner product ipAt(I, J, N, D, aX, aY)
    have hsmall : logFour D₀ < G.m₀ := by
      by_contra hc
      exact hflag (by simpa using (hR.large (by omega)).1)
    refine Ends.callTo (hip N D₀ aX aY X Y U μ I J hin.one_le_D hR.matX hR.matY hin.absX hin.absY
      (by omega) (by omega) hlim.ip _ (by omega)) ?_
      (hT := by simp [tQuery31, if_pos hsmall]; omega)
    rintro r μ' ⟨hr, rfl⟩
    exact ⟨hr, hR, .refl⟩

/-! ## The preprocessing: text and interface -/









namespace Pre31



















end Pre31















































end Light.Sec4

end
end

section


/-!
# An entry of the product as an inner product

Proof of Corollary 26: "(For m < 60, D is bounded by a constant, and the corollary holds
trivially.)"; proof of Corollary 31: "for smaller m the corollary again holds trivially". In the
programs a query then computes an inner product, of a bounded number D of summands. The routine adds
the D products X[I, s] Y[s, J]. `ipPart` is the sum of the first s of them, with its recursion
(`ipPart_succ`), its bound (`abs_ipPart_le`) and its last value (`ipPart_full`); `ipAt_meets` is the
specification.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec Finset

namespace IpAt















end IpAt











section
variable {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (I J : Fin N)




theorem ipPart_full : ipPart X Y I J D₀ = (X * Y) I J := by
  rw [Matrix.mul_apply, ipPart, Finset.sum_range]
  exact Finset.sum_congr rfl fun i _ => by simp

theorem ipPart_succ {s : ℕ} (hs : s < D₀) :
    ipPart X Y I J (s + 1) = ipPart X Y I J s + X I ⟨s, hs⟩ * Y ⟨s, hs⟩ J := by
  rw [ipPart, Finset.sum_range_succ, dif_pos hs]
  rfl

variable {X Y}

theorem abs_mul_entry_le {U : ℤ} (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U) (s : Fin D₀) :
    |X I s * Y s J| ≤ U * U := by
  rw [abs_mul]
  exact mul_le_mul (hX _ _) (hY _ _) (abs_nonneg _) (le_trans (abs_nonneg _) (hX I s))

theorem abs_ipPart_le {U : ℤ} (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U) :
    ∀ s ≤ D₀, |ipPart X Y I J s| ≤ s * (U * U)
  | 0, _ => by simp [ipPart]
  | s + 1, hs => by
    rw [ipPart_succ X Y I J hs]
    refine (abs_add_le _ _).trans ?_
    have := abs_ipPart_le hX hY s (by omega)
    have := abs_mul_entry_le I J hX hY ⟨s, hs⟩
    push_cast
    linarith

end

theorem ipAt_meets {lim : Limits} {P : Program} (hP : P[Proc.ipAt]? = some ipAtBody)
    (hstd : Std lim) : IpAtSpec lim P := by
  intro N D₀ aX aY X Y U μ I J hD hmX hmY hX hY sX sY hU
  refine fun d _ => ⟨ipAtBody, hP, ?_⟩
  have hw := hstd.space_le
  have h100 := hstd.const_le
  have hrow : (I : ℕ) * D₀ + D₀ ≤ N * D₀ := Nat.mul_add_le_mul I.isLt le_rfl
  have hcol : (J : ℕ) < N := J.isLt
  have hN : N ≤ D₀ * N := Nat.le_mul_of_pos_left _ hD
  -- every partial sum and every product fits in a word
  have hfits : ∀ s ≤ D₀, |ipPart X Y I J s| ≤ lim.word := fun s hs =>
    (abs_ipPart_le I J hX hY s hs).trans (le_trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hs)
        (le_trans (abs_nonneg _) (abs_mul_entry_le I J hX hY ⟨0, hD⟩))) hU)
  have hprod : ∀ s : Fin D₀, |X I s * Y s J| ≤ lim.word := fun s =>
    (abs_mul_entry_le I J hX hY s).trans (le_trans (le_mul_of_one_le_left
      (le_trans (abs_nonneg _) (abs_mul_entry_le I J hX hY s)) (by exact_mod_cast hD)) hU)
  unfold ipAtBody tIpAt
  -- s := 0 ; sum := 0 ; row := aX + I * D ; col := aY + J
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen 0 ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen 0 ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (aX + (I : ℕ) * D₀ : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.setToThen
          (aY + (J : ℕ) : ℕ)
            -- while s < D: sum := sum + mem[row + s] * mem[col + s * N] ; s := s + 1
            
          ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  -- while s < D: sum := sum + mem[row + s] * mem[col + s * N] ; s := s + 1
  refine Ends.next _ (Ends.whileBlock (fun s σ => σ = ⟨frame [(I : ℕ), (J : ℕ), N, D₀, aX, aY, s,
      ipPart X Y I J s, ((aX + (I : ℕ) * D₀ : ℕ) : ℤ), ((aY + (J : ℕ) : ℕ) : ℤ)], μ⟩) D₀
    (by simp [ipPart]) ?round ?done (hT := le_rfl))
  case round =>
    rintro s _ hs rfl
    have hcell : s * N + N ≤ D₀ * N := Nat.mul_add_le_mul hs le_rfl
    have hx : μ (aX + (I : ℕ) * D₀ + s) = X I ⟨s, hs⟩ := hmX I ⟨s, hs⟩
    have hy : μ (aY + (J : ℕ) + s * N) = Y ⟨s, hs⟩ J := by
      rw [← hmY ⟨s, hs⟩ J]
      congr 1
      change aY + (J : ℕ) + s * N = aY + s * N + (J : ℕ)
      omega
    have haddrX : ((aX : ℤ) + (I : ℕ) * D₀ + s).toNat = aX + (I : ℕ) * D₀ + s := by
      rw [← Int.toNat_natCast (aX + (I : ℕ) * D₀ + s)]; push_cast; rfl
    have haddrY : ((aY : ℤ) + (J : ℕ) + s * N).toNat = aY + (J : ℕ) + s * N := by
      rw [← Int.toNat_natCast (aY + (J : ℕ) + s * N)]; push_cast; rfl
    have hsum := abs_le.1 (hfits (s + 1) hs)
    have hxy := abs_le.1 (hprod ⟨s, hs⟩)
    rw [ipPart_succ X Y I J hs] at hsum ⊢
    generalize ipPart X Y I J s = S at hsum ⊢
    generalize X I ⟨s, hs⟩ = x at hx hsum hxy ⊢
    generalize Y ⟨s, hs⟩ J = y at hy hsum hxy ⊢
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp; omega, by (((try have := Light.Std.space_le (by assumption)));
                                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, haddrX, haddrY, hx, hy] <;>
                                                                                                      omega)),
      by simp [update_frame_setLocal, haddrX, haddrY, hx, hy]⟩
  case done =>
    rintro _ rfl
    -- return sum
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp, Ends.setTo (ipPart X Y I J D₀) ⟨ipPart_full X Y I J, rfl⟩⟩

end Light.Sec4

end
end

section


/-!
# Running the word RAM: words, steps, pieces of code, straight-line code, branches

What the proofs about compiled code need to know about the word RAM in which the paper's claims are
stated.

* **Words.**  `wd W v` is the word of the integer v.  If v is in the range of signed words
  (`InRange`), the word gives back v (`toInt_wd`).
* **Steps.**  The end statement defines only whole runs (`exec`).  A configuration (`Cfg`) and a
  single step (`step`) are defined here; `exec_succ_of_step` and `exec_succ_of_verdict` say that
  `exec` takes one step at a time.
* **Runs.**  `Steps P n c c'`: exactly n steps lead from c to c', none of them a verdict.
  Runs are composed by `Steps.trans`; a run that ends before a verdict gives the value of `exec`
  (`exec_of_steps`), and more time does not change that value (`exec_mono`).
* **Code.**  `CodeAt P pos l`: the program P has the instructions of the list l from position pos
  on.
* **Straight-line code.**  Six instructions only change the memory (`Straight`, `effect`); a list
  of them runs through in its length (`steps_straight`).
* **Known numbers.**  On cells that hold the words of known numbers, an instruction writes the word
  of a known number: `effect_add`, …, `effect_store` for the memory; `steps_add`, `steps_sub`,
  `steps_load`, `steps_store` for the step.
* **Branches and verdicts.**  A branch on a cell that holds a known number is `steps_bltz`;
  `Steps.branch` turns its two outcomes into the two outcomes of a test.  The verdicts are
  `step_accept` and `step_reject`.
* **Framing.**  `AgreeOutside s m m'`: the memories m and m' are equal outside the set s of cells.
  For code without stores such a set can be read off the text (`WritesIn`, `agreeOutside_effects`).
-/

@[expose] public section

namespace ThreeSumApsp.WordRam

open EndStatement (Instr exec loadWords)

variable {W : ℕ} {P : List Instr}

/-! ## Words -/








































/-! ## Configurations and single steps -/






















/-! ## Runs -/


















































/-! ## Pieces of code -/





































/-! ## Straight-line code -/





















































/-! ## Single instructions on cells that hold known numbers -/

section known

variable {m : ℤ → BitVec W} {i j k a b : ℤ}

















































end known

/-! ## Branches and verdicts -/























/-! ## Framing -/

section framing

variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}






















































end framing

end ThreeSumApsp.WordRam

end
end

section


/-!
# Theorem 30, the offline form (9): preprocess, then one query for each wanted position

Theorem 30: "In particular, for every set W of positions of an N × N matrix, the entries (XY)[I, J],
(I, J) ∈ W, can be computed deterministically in time
O(L |W| ∑_{d=0}^{t} α_d + L m ρ^t/(1 - ρ) N² + N · 10^L/(√K N₀))."

wantedCore is relocatable: it receives the addresses of the matrices, of the two lists of indices,
of the output and of the free block. It meets its specification `WantedCoreSpec` in every program
that meets those of preCore and queryAt (`wantedCore_spec`): one call of preCore, then a loop whose
round asks one query and stores the answer (`wantedAsk_ends`), with the invariant `Answered`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## One query for each wanted position: the invariant -/

section
variable {Ready : (ℕ → ℤ) → Prop} {Kept Quiet : ℕ → Prop} {out i : ℕ} {ans : List ℤ}
  {μ μ' μ'' : ℕ → ℤ}










/-- One round: a query that leaves the cells in Quiet alone, among them the output and the cells in
Kept, and the store of its answer behind the answers that are there. -/
theorem Answered.step (h : Answered Ready Kept out ans μ i μ') (hi : i < ans.length)
    (hquery : SameOn Quiet μ' μ'') (hout : ∀ j < i, Quiet (out + j)) (hkept : ∀ a, Kept a → Quiet a)
    (hready : Ready (Function.update μ'' (out + i) ans[i])) :
    Answered Ready Kept out ans μ (i + 1) (Function.update μ'' (out + i) ans[i]) := by
  have hlen : (ans.take i).length = i := by rw [List.length_take, Nat.min_eq_left hi.le]
  refine ⟨hready, ?_, ?_⟩
  · have hsnoc := (h.answers.of_sameOn hquery fun j hj => hout j (hlen ▸ hj)).snoc ans[i]
    rw [hlen] at hsnoc
    rwa [List.take_add_one, List.getElem?_eq_getElem hi]
  · exact ((h.same.mono fun a ha => ⟨by have := ha.1; omega, ha.2⟩).then hquery
      fun a ha => ⟨ha, hkept a ha.2⟩).write (by omega) _

/-- A cell of a list that stood in the memory at the start, away from the answers and in Kept, still
holds its entry. -/
theorem Answered.read (h : Answered Ready Kept out ans μ i μ') {a j : ℕ} {l : List ℤ}
    (hl : Seg μ a l) (hj : j < l.length) (hoff : Outside out i (a + j)) (hkept : Kept (a + j)) :
    μ' (a + j) = l[j] :=
  (h.same _ ⟨hoff, hkept⟩).trans (hl.get hj)

/-- After the last round all answers are in place. -/
theorem Answered.all (h : Answered Ready Kept out ans μ ans.length μ') : Seg μ' out ans := by
  simpa using h.answers

end

/-! ## The routine -/



namespace WantedCore




















end WantedCore


















section
variable {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY aI aJ out b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {W : List (Fin p.N × Fin p.N)} {μ μ' μ'' : ℕ → ℤ}


















end






















































































end Light.Sec4

end
end

section


/-!
# Section 4.4, the offline form: preprocess, then one query for each wanted position

Corollary 26: "Hence, for every set W of positions of an N × N matrix, the entries (XY)[I, J], (I,
J) ∈ W, can be computed deterministically in O(|W| D^{0.437} + N²/D^{0.063}) time". Its proof: "The
bound for a set W follows by asking |W| queries." Proof of Theorem 25: "ask one query for each
position of W"; for Corollary 32 the paper uses "the same argument", "With Corollary 31 in place of
Theorem 24".

offline32(N, D, w, U, x, y, wi, wj, out, fr) preprocesses the matrices at x and y (pre31, which uses
the cells from the free pointer fr on) and then asks one query for each of the w positions, whose
rows are at wi and whose columns are at wj; the answers go to out. The arguments are those of the
task `thinTask`. The text `offline32Body`, with the round `offlineAsk32` of its loop, serves all
rational parameters c and θ: they are in the body of the procedure pre31 (`pre31Body`).

A round adds one answer (`offlineAsk32_ends`), with the invariant `Answered` that the offline form
of Theorem 30 uses too, and the routine meets its specification `OfflineSpec32` for all parameters G
(`offline32_meets`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}

/-! ## The text -/






namespace Offline32

















end Offline32















/-! ## What it does -/

/-- What a query needs depends only on the cells of X, of Y, and on the cells from fr on. -/
theorem ready31_congr (h : Ready31 G X Y aX aY fr μ)
    (hX : ∀ a, aX ≤ a → a < aX + N * D₀ → μ' a = μ a)
    (hY : ∀ a, aY ≤ a → a < aY + D₀ * N → μ' a = μ a) (hfr : ∀ a, fr ≤ a → μ' a = μ a) :
    Ready31 G X Y aX aY fr μ' := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun hs => ?_, fun hl => ?_⟩
  · rw [hX _ (by omega) ?_]
    · exact h.matX i j
    · have := Nat.mul_add_le_mul i.isLt (le_refl D₀)
      have := j.isLt
      omega
  · rw [hY _ (by omega) ?_]
    · exact h.matY i j
    · have := Nat.mul_add_le_mul i.isLt (le_refl N)
      have := j.isLt
      omega
  · rw [hfr _ le_rfl]
    exact h.small hs
  · obtain ⟨h1, h2, h3⟩ := h.large hl
    refine ⟨by rw [hfr _ le_rfl]; exact h1, by rw [hfr _ (by omega)]; exact h2,
      dsReady_congr h3 fun a ha => hfr a ?_⟩
    unfold blockAt at ha
    omega





































/-- The specification holds for the program with more procedures appended. -/
theorem OfflineSpec32.append {c : ℕ} (h : OfflineSpec32 lim P c G) (R : Program) :
    OfflineSpec32 lim (P ++ R) c G :=
  fun N D₀ aX aY aI aJ out fr X Y U u μ WI WJ hg hin d hd =>
    (h N D₀ aX aY aI aJ out fr X Y U u μ WI WJ hg hin d hd).append R

/-- **One round**: the answer for position i joins the answers that are there. -/
theorem offlineAsk32_ends (hq : QuerySpec31 lim P G) {aI aJ out d : ℕ}
    {u : ℤ} {WI WJ : List ℕ} (hg : Input31 lim G X Y aX aY fr U)
    (hin : OfflineInput32 X Y aX aY aI aJ out fr WI WJ μ) (hd : d + 4 ≤ lim.depth) {i : ℕ}
    (hi : i < WI.length) (r : ℤ)
    (hinv : Answered (Ready31 G X Y aX aY fr) (· < fr) out
      ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) μ i μ') :
    Ends lim P d offlineAsk32 ⟨frame [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr, i, r], μ'⟩
      (tQuery31 G D₀ + 20) fun σ' => ∃ (r' : ℤ) (μ'' : ℕ → ℤ),
        σ' = ⟨frame [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr, i, r'], μ''⟩ ∧
        Answered (Ready31 G X Y aX aY fr) (· < fr) out
          ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) μ (i + 1) μ'' := by
  have hw := hg.lim.std.space_le
  have hspace := hg.lim.space
  have hfr3 := add_three_le_structEnd G N D₀ fr
  have hlen := hin.length_eq
  have hrows := hin.rows_le
  have hcols := hin.cols_le
  have hout := hin.out_le
  have hiJ : i < WJ.length := by omega
  have hIN : WI[i] < N := hin.rows_lt _ (List.getElem_mem hi)
  have hJN : WJ[i] < N := hin.cols_lt _ (List.getElem_mem hiJ)
  -- the two indices are still in place
  have hrow : μ' (aI + i) = ((WI[i] : ℕ) : ℤ) :=
    (hinv.read hin.rows (j := i) (by simpa using hi)
      (by rcases hin.out_rows with h | h <;> omega) (by omega)).trans (List.getElem_map _)
  have hcol : μ' (aJ + i) = ((WJ[i] : ℕ) : ℤ) :=
    (hinv.read hin.cols (j := i) (by simpa using hiJ)
      (by rcases hin.out_cols with h | h <;> omega) (by omega)).trans (List.getElem_map _)
  -- Res := query31(mem[Rows + Pos], mem[Cols + Pos], N, D, x, y, fr)
  refine Ends.callToThen (hq N D₀ aX aY fr X Y U μ' ⟨WI[i], hIN⟩ ⟨WJ[i], hJN⟩ hg hinv.ready _
    (by omega)) ?_
    (ha := by (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul, hrow, hcol] <;> omega)))
  rintro _ μ₂ ⟨rfl, hready, hquery⟩
  -- mem[Out + Pos] := Res
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine
        Light.Ends.storeToThen (out + i) ((X * Y) ⟨WI[i], hIN⟩ ⟨WJ[i], hJN⟩) ?_ ?_
          ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  have hstep := hinv.step (by simpa [hlen] using hi) hquery (fun j hj => Or.inl (by omega))
    (fun a ha => Or.inl (by omega)) (ready31_congr hready
      (fun a h1 h2 => Function.update_of_ne (by rcases hin.out_matX with h | h <;> omega) _ _)
      (fun a h1 h2 => Function.update_of_ne (by rcases hin.out_matY with h | h <;> omega) _ _)
      fun a ha => Function.update_of_ne (by omega) _ _)
  rw [List.getElem_map, List.getElem_zip, entryN, dif_pos ⟨hIN, hJN⟩] at hstep
  exact ⟨_, _, rfl, hstep⟩

theorem offline32_meets {c : ℕ} (hP : P[Proc.offline32]? = some offline32Body)
    (hpre : PreSpec31 lim P c G) (hq : QuerySpec31 lim P G) : OfflineSpec32 lim P c G := by
  intro N D₀ aX aY aI aJ out fr X Y U u μ WI WJ hg hin
  refine fun d hd => ⟨offline32Body, hP, ?_⟩
  have hw := hg.lim.std.space_le
  have hspace := hg.lim.space
  have hfr3 := add_three_le_structEnd G N D₀ fr
  have hlen := hin.length_eq
  have hout := hin.out_le
  have hzip : (WI.zip WJ).length = WI.length := by simp [hlen]
  -- Res := pre31(N, D, x, y, fr)
  refine Ends.callToThen (hpre N D₀ aX aY fr X Y U μ hg hin.matX hin.matY _ (by omega)) ?_
    (hT := by simp [tOffline32]; omega)
  rintro r μ₁ ⟨hready, hblock⟩
  -- for Pos < Count: offlineAsk32
  refine Ends.for (fun i σ => ∃ (r : ℤ) (μ' : ℕ → ℤ),
      σ = ⟨frame [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr, i, r], μ'⟩ ∧
      Answered (Ready31 G X Y aX aY fr) (· < fr) out ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) μ
        i μ')
    WI.length (tQuery31 G D₀ + 20) ?start ?round ?done ?bound
    (hT := by simp [tOffline32]; ring_nf; omega)
  case start =>
    exact ⟨r, μ₁, by rw [update_frame_setLocal]; rfl, hready, Seg.nil,
      SameOn.mono hblock fun a ha => Or.inl ha.2⟩
  case bound =>
    rintro i _ - - ⟨r, μ', rfl, -⟩
    simp
  case done =>
    rintro _ - ⟨r, μ', rfl, hinv⟩
    rw [← hzip, ← List.length_map (as := WI.zip WJ) fun q => entryN X Y q.1 q.2] at hinv
    refine ⟨hinv.all, fun a ha hoff => hinv.same a ⟨?_, ha⟩⟩
    simpa [hlen] using hoff
  case round =>
    rintro i _ hi - ⟨r, μ', rfl, hinv⟩
    refine (offlineAsk32_ends hq hg hin (by omega) hi r hinv).mono le_rfl ?_
    rintro _ ⟨r', μ'', rfl, hinv'⟩
    exact ⟨by simp, r', μ'', by rw [update_frame_setLocal]; rfl, hinv'⟩

end Light.Sec4

end
end

section


/-!
# The routines of Section 4, assembled

The fourteen routines with the numbers 40 to 53, as a list (procs40), and the theorem that every
program that holds them at these numbers (Has40) meets all their specifications (specs40). Each
routine is proved under the specifications of the routines that it calls; here these assumptions are
discharged, in the order in which the routines call each other. For the programs of Theorem 30, its
offline form and Corollary 26, which hold the fourteen routines behind forty others
(has40_of_append), this gives the specifications of the two routines that know the memory map:
preCoreSpec_of and preCoreSpec_all for the preprocessing, queryAtSpec_all for a query.
-/

@[expose] public section

namespace Light.Sec4

































































/-- A query at a given place of the memory, for all limits. -/
theorem queryAtSpec_all {P : Program} (h : Has40 P)
    (h55 : P[Proc.queryAt]? = some queryAtBody) : ∀ lim, QueryAtSpec lim P :=
  fun _ p t hmL aX aY b0 X Y U μ I J ht hlim =>
    queryAt_spec h55 (specs40 h hlim.std).outDigits
      (specs40 h hlim.std).queryCore p t hmL aX aY b0 X Y U μ I J ht hlim

/-- A list that has forty procedures, then the routines of Section 4, then anything, holds them at
their numbers. -/
theorem has40_of_append {A B : List Stmt} (hA : A.length = 40) : Has40 (A ++ procs40 ++ B) := by
  intro i hi
  have hlen : procs40.length = 14 := rfl
  rw [List.append_assoc, List.getElem?_append_right (by omega), hA, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by omega)]

end Light.Sec4

end
end

section


/-!
# Theorem 30 on the word RAM: the program

`program30` is the list of procedures: those of Section 2 (numbers 0 to 28, of which the
preprocessing uses the shared stage), the routines of Section 4 (40 to 53), preCore, queryAt and the
two procedures of the offline form (54 to 57), and the two main procedures of Theorem 30 (80 and
81); the unused numbers hold the empty statement.

The first 58 procedures (`base58`) are also the beginning of the programs for Corollaries 26, 31
and 32.  So the assumptions of the earlier files are discharged for every program `base58 ++ R` that
begins with them: it meets the specifications of the preprocessing and of a query at a given place
of the memory (`preCore_base58`, `queryAt_base58`).  With `theorem_30_of` and `theorem_30_wanted_of`
this gives Theorem 30 and its offline form without hypotheses (`wordRam_theorem_30`,
`wordRam_theorem_30_wanted`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.WordRam








theorem length_base58 : base58.length = 58 := rfl

/-- A procedure of base58 is a procedure, with the same number, of every program that begins with
base58. -/
theorem at_base58 {p : ℕ} {body : Stmt} (h : base58[p]? = some body) (R : Program) :
    (base58 ++ R)[p]? = some body :=
  getElem?_append_of_eq_some h R




theorem has40_base58 (R : Program) : Has40 (base58 ++ R) := by
  have h := has40_of_append (A := Sec2.programThin ++ List.replicate 11 .skip)
    (B := [preCoreBody, queryAtBody, wantedCoreBody, wantedMainBody] ++ R) rfl
  rwa [← List.append_assoc] at h
















/-- **A query at a given place of the memory**, in every program that begins with base58. -/
theorem queryAt_base58 (R : Program) : ∀ lim, QueryAtSpec lim (base58 ++ R) :=
  queryAtSpec_all (has40_base58 R) (at_base58 rfl R)




end Light.Sec4

end
end

section


/-!
# Corollaries 26, 31 and 32: the concrete program for given parameters

program31 G = base58 (Theorem 5's and Theorem 30's procedures, numbers 0 to 57) followed by the
procedures 58 to 73 of Section 4.4 (`procs31`): copying, filling, m = ⌈log₄ D⌉, padding and the
inner product; the preprocessing pre31Body G at 64 and the query; their main procedures; the offline
routine and its main procedure; the solver of Corollary 26 for all instances with its test; and the
two procedures for L = ⌈am/b⌉ and t = ⌈pm/q⌉ at 72 and 73. The specifications of the preprocessing,
the query and the offline routine hold for it, for all limits, without hypotheses. At the parameters
of Corollary 26 it is `program26`.

With the two end theorems for light programs and the compiler this gives the two statements about
the word RAM from which Corollaries 26, 31 and 32 follow: on every domain of inputs, and for all
bounds that dominate the two costs of Theorem 30 at the parameters G (`CostsWithin`), the compiled
program is a data structure (`isDataStructure_of_costsWithin`) and solves the offline problem
(`solves_of_costsWithin`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.WordRam

/-! ## Two procedures for Corollary 26

The program carries them for all parameters G. What they do at the parameters of Corollary 26 is
proved in `regimeTest26_meets` and `allInstances26_solves`. -/












/-! ## The program -/










/-- The routines stand at their numbers. -/
theorem program31_at (G : RatParams) (n : ℕ) {body : Stmt} (hn : 58 ≤ n := by norm_num)
    (h : (procs31 G)[n - 58]? = some body := by rfl) : (program31 G)[n]? = some body := by
  rw [program31, List.getElem?_append_right (by rw [length_base58]; exact hn), length_base58]
  exact h
















/-- **A query**, for all limits. -/
theorem query31_program31 (G : RatParams) : ∀ lim, QuerySpec31 lim (program31 G) G := by
  intro lim N D₀ aX aY fr X Y U μ I J hin
  have hip : IpAtSpec lim (program31 G) := ipAt_meets (program31_at G Proc.ipAt) hin.lim.std
  exact query31_meets G (program31_at G Proc.query31) (queryAt_base58 _ lim) hip
    N D₀ aX aY fr X Y U μ I J hin

/-- **The offline routine**, for all limits. -/
theorem offline32_program31 (G : RatParams) : ∀ lim, OfflineSpec32 lim (program31 G) cShared30 G :=
  fun lim => offline32_meets (program31_at G Proc.offline32) (pre31_program31 G lim)
    (query31_program31 G lim)













/-! ## The program on the word RAM -/







































end Light.Sec4

end
end

section


/-!
# Corollary 26, the offline form, on all instances

Corollary 26 is about matrices with N ≥ D^18. A solver that other procedures call has to be right on
every instance. allInstances26(N, D, w, U, x, y, wi, wj, out, fr) tests whether D^18 ≤ N, calls the
offline routine offline32 if so and the brute force if not. The texts are `allInstances26Body` and
`regimeTest26Body`.

* *The routine.* It solves the task `thinTask` on every instance, within the time
  `allInstancesTime26` and the need `allInstancesNeed26` (`allInstances26_solves`). It tests whether
  D^18 ≤ N (`regimeTest26_meets`). In that regime it calls the offline routine of Corollary 26,
  whose demands on the limits are covered by the need (`lim31_of_need`, `offline32_meets_thinTask`);
  outside it calls the brute force.
* *The time in the regime.* For N ≥ D^18 the time is O(w D^{0.437} + N²/D^{0.063}), the bound of
  Corollary 26: the time of the offline routine is at most a constant times tp + w tq for all bounds
  that dominate the two costs of Theorem 30 (`exists_tOffline32_le`), and in the regime the two
  bounds of Corollary 26 do (`regime26`).
* *The need is polynomial in the parameters.* Every summand of the need is a numeral times a product
  of at most 20 factors N + 1, D and U. With Q = (N + 1) (D + 1) (w + 1) (U + 1) each factor is at
  most Q, so each product is at most Q^20 (`le_pow_twenty`). So the largest number, the cells and
  the levels of calls are at most 2^11 Q^20 (`word_le`, `cells_le`, `depth_le`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Time and need -/


















/-! ## The test -/





















/-! ## The limits -/

section need

variable {lim : Limits} {N D₀ w U fr d : ℕ}










































































end need

/-! ## The matrices of an instance -/



































/-! ## The routine -/


























































































/-! ## The time in the regime -/


















/-! ## The need is polynomial in the parameters -/

private theorem le_pow_twenty {Q x : ℕ} (hQ : 1 ≤ Q) (i : ℕ) (hi : i ≤ 20) (h : x ≤ Q ^ i) :
    x ≤ Q ^ 20 :=
  h.trans (Nat.pow_le_pow_right hQ hi)

section summands

variable {N D U Q : ℕ}

/-- The largest number that allInstances26 forms. -/
private theorem word_le (hN : N + 1 ≤ Q) (hD : D ≤ Q) (hU : U ≤ Q) :
    1000 + 100 * D + N * D + D * (U * U) + ((N + 1) ^ 5) ^ 3 * (U * U) +
      7 * ((N + 1) ^ 5 * U) + 10 * (N + 1) ^ 5 ≤ 2 ^ 11 * Q ^ 20 := by
  have hQ : 1 ≤ Q := by omega
  have hN' : N ≤ Q := by omega
  have h1 : 1 ≤ Q ^ 20 := Nat.one_le_pow _ _ hQ
  have hD1 : D ≤ Q ^ 20 := le_pow_twenty hQ 1 (by norm_num) (by simpa using hD)
  have hND : N * D ≤ Q ^ 20 := le_pow_twenty hQ 2 (by norm_num) <|
    calc N * D ≤ Q * Q := by gcongr
      _ = Q ^ 2 := by ring
  have hDUU : D * (U * U) ≤ Q ^ 20 := le_pow_twenty hQ 3 (by norm_num) <|
    calc D * (U * U) ≤ Q * (Q * Q) := by gcongr
      _ = Q ^ 3 := by ring
  have hvalue : ((N + 1) ^ 5) ^ 3 * (U * U) ≤ Q ^ 20 := le_pow_twenty hQ 17 (by norm_num) <|
    calc ((N + 1) ^ 5) ^ 3 * (U * U) ≤ (Q ^ 5) ^ 3 * (Q * Q) := by gcongr
      _ = Q ^ 17 := by ring
  have henc : (N + 1) ^ 5 * U ≤ Q ^ 20 := le_pow_twenty hQ 6 (by norm_num) <|
    calc (N + 1) ^ 5 * U ≤ Q ^ 5 * Q := by gcongr
      _ = Q ^ 6 := by ring
  have hpow : (N + 1) ^ 5 ≤ Q ^ 20 := le_pow_twenty hQ 5 (by norm_num) (by gcongr)
  -- 1000 + 100 + 1 + 1 + 1 + 7 + 10 = 1120 ≤ 2^11
  omega

/-- The cells that allInstances26 uses. -/
private theorem cells_le (hN : N + 1 ≤ Q) (hD : D ≤ Q) :
    4 + N + 8 * (N * D) + 222 * ((N + 1) ^ 5) ^ 4 ≤ 2 ^ 11 * Q ^ 20 := by
  have hQ : 1 ≤ Q := by omega
  have hN' : N ≤ Q := by omega
  have h1 : 1 ≤ Q ^ 20 := Nat.one_le_pow _ _ hQ
  have hN1 : N ≤ Q ^ 20 := le_pow_twenty hQ 1 (by norm_num) (by simpa using hN')
  have hND : N * D ≤ Q ^ 20 := le_pow_twenty hQ 2 (by norm_num) <|
    calc N * D ≤ Q * Q := by gcongr
      _ = Q ^ 2 := by ring
  have hblock : ((N + 1) ^ 5) ^ 4 ≤ Q ^ 20 :=
    calc ((N + 1) ^ 5) ^ 4 ≤ (Q ^ 5) ^ 4 := by gcongr
      _ = Q ^ 20 := by ring
  omega

/-- The levels of calls that allInstances26 needs. -/
private theorem depth_le (hQ : 1 ≤ Q) (hD : D ≤ Q) : 84 * D + 12 ≤ 2 ^ 11 * Q ^ 20 := by
  have h1 : 1 ≤ Q ^ 20 := Nat.one_le_pow _ _ hQ
  have hD1 : D ≤ Q ^ 20 := le_pow_twenty hQ 1 (by norm_num) (by simpa using hD)
  omega

end summands

/-- Three of four positive factors are at most the product. -/
private theorem le_prod_four {a b c e : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    a ≤ a * (b * (c * e)) ∧ b ≤ a * (b * (c * e)) ∧ e ≤ a * (b * (c * e)) :=
  ⟨Nat.le_mul_of_pos_right a (by positivity),
    (Nat.le_mul_of_pos_right b (by positivity)).trans (Nat.le_mul_of_pos_left _ ha),
    ((Nat.le_mul_of_pos_left e hc).trans (Nat.le_mul_of_pos_left _ hb)).trans
      (Nat.le_mul_of_pos_left _ ha)⟩

/-- The need is polynomial in the parameters. -/
theorem allInstancesNeed26_poly : PolyNeedN allInstancesNeed26 := by
  refine ⟨11, 20, fun ps => ?_⟩
  match ps with
  | [N, D, w, U] =>
    obtain ⟨hN, hD, hU⟩ := le_prod_four N.succ_pos D.succ_pos w.succ_pos U.succ_pos
    rw [show polyBound 11 20 [N, D, w, U] =
      2 ^ 11 * ((N + 1) * ((D + 1) * ((w + 1) * (U + 1)))) ^ 20 by simp [polyBound]]
    generalize (N + 1) * ((D + 1) * ((w + 1) * (U + 1))) = Q at *
    exact ⟨word_le hN (by omega) (by omega), cells_le hN (by omega), depth_le (by omega) (by omega)⟩
  | [] | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ :: _ =>
    exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

end Light.Sec4

end
end

section


/-!
# Corollary 26, the offline form, for programs of the light language

Corollary 26: "Hence, for every set W of positions of an N × N matrix, the entries (XY)[I, J], (I,
J) ∈ W, can be computed deterministically in O(|W| D^{0.437} + N²/D^{0.063}) time". This is
`Claim.Corollary_26_wanted`, here with "is solved in time T" read as a statement about programs of
the light language (`claim_corollary_26_wanted`).

The program is `program26`: for m = ⌈log₄ D⌉ ≥ 60 it builds and asks the data structure of Theorem
30 with L = 21 m and t = ⌈m/9⌉, and for m < 60 it computes inner products. The procedure
allInstances26 of that program solves the task on all instances (`allInstances26_program26`), with a
polynomially bounded need (`allInstancesNeed26_poly`), and for N ≥ D^18 its time is within the bound
(`allInstancesTime26_le`).

This is the form of Corollary 26 on which Corollary 16, and through it the second bounds of Theorems
19 and 22, rest: a procedure that other procedures call. The statement about one program that reads
the input of the problem is `wordRam_corollary_26_wanted`.
-/

public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec



/-- **The procedure allInstances26 of `program26` solves the task on all instances**: the program
holds allInstances26, regimeTest26 and the brute force at their numbers. -/
theorem allInstances26_program26 : SolvesN thinTask program26 Proc.allInstances26
    (allInstancesTime26 cShared30) allInstancesNeed26 :=
  allInstances26_solves (program31_at _ Proc.allInstances26) (program31_at _ Proc.regimeTest26)
    (at_base58 rfl _) fun R lim => (offline32_program31 _ lim).append R



end Light.Sec4

end
end

section


/-!
# From a realized running time to a program with the paper's bound

A claim gives a running time `T` with `T ≤ C X`, where `X` is the bound that the paper prints, and
`RealizedWithin` gives a program that takes `c T + c` steps.  This file puts the two together.

* Bounds in several parameters, valid on a domain on which `X ≥ 1`: `exists_solves`, and
  `exists_solves_nonneg` with `exists_solves_pair` for two programs with one slope and one constant.
* Bounds `O(n^a (log n)^e)` in one size, valid for all large `n`: `solvedAt_of_realized`, and for
  every exponent `κ` of the magnitude `solvedInTime_of_claim` and `solvedInPolylogTime_of_claim`.
* An instance with numbers bounded by `n^κ` is also one with numbers bounded by `n^κ'`, `κ ≤ κ'`
  (`solvedInTimeAt_mono`), so that a bound for all `κ ≥ 1` is a bound for all `κ`
  (`solvedInTime_of_one_le`).
-/

public section

namespace ThreeSumApsp.FromClaims

open ThreeSumApsp.WordRam
open EndStatement (Instr)

/-! ## Bounds on a domain -/




















































/-! ## Bounds in one size, for all large sizes -/

























































end ThreeSumApsp.FromClaims

end
end

section


/-!
# Running-time claims of Section 3.1: Corollaries 15 and 16

All lemmas are about an arbitrary interpretation `M : DetTimeModel` of "is solved in time T".

* Corollary 15, first case, from Theorem 5 ("Apply Theorem 5 with N = n to the two biadjacency
  matrices"): `Corollary15.first_of_theorem_5`.
* Corollary 15, general case ("splitting W into sets of at most n²/√D query pairs"):
  `Corollary15.general_of_theorem_5`.  One call costs `O(n² log² D / D^{1/18})`, and all calls
  with the overhead cost `O((n² + |W| √D) log² D / D^{1/18})` (`dominated_calls`).
* Corollary 16 from Corollary 26 ("This is Corollary 26 with N = n"):
  `Corollary16.of_corollary_26`.

In each deduction the overheads `n D`, `|W|` and `1` of writing the matrices and copying the answers
are at most the bound of the corollary, because `n ≥ D^18`.  The bounds are added up by the calculus
of `Dominated` on the parameters `n`, `D`, `w`.
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## The calculus on the parameters `n`, `D`, `w` -/













/-! ## Corollary 15, the first case -/























/-! ## Corollary 15, the general case -/





















































/-! ## Corollary 16 -/



end ThreeSumApsp

end
end

section


/-!
# Corollaries 15 and 16 on the word RAM

The route, as in the paper.  The number of triangles through a query pair is an entry of the product
of the two biadjacency matrices, and detection follows from counting.  So Theorem 5 gives the first
case of Corollary 15; splitting the query pairs into pieces gives the general case; and the offline
form of Corollary 26 gives Corollary 16.  These are claims about programs of the light language
(`claim_corollary_15_first`, `claim_corollary_15`, `claim_corollary_16`).  The outermost procedures
for the input layout and the compiler (`Light.Sec3.realized_lopCount`,
`Light.Sec3.realized_lopDetect`, together `lopRealized`) carry them to the word RAM.
-/

public section

open ThreeSumApsp ThreeSumApsp.WordRam

namespace Light.Sec3


















end Light.Sec3

namespace ThreeSumApsp









end ThreeSumApsp

end
end

section


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




































/-! ### Logarithms -/







/-! ### Powers of `D` in terms of `n` -/









/-! ### The four terms of the running time

`Λ` is the logarithmic factor of the result, `log² n` or `log n`. -/









end Choice



end Theorem19

end ThreeSumApsp

end
end

section


/-!
# Theorem 19 and Remark 20: Exact Triangle in truly subcubic time (Section 3.3)

Theorem 19 applies the reduction of Theorem 17 with `D` about `n^{1/18}` and `g = ⌈D^η⌉`, and solves
each instance by a corollary of Section 3.1: by Corollary 15 with `η = 1/36`, where `D` is the
largest power of four with `D ≤ n^{1/18}`, and by Corollary 16 with `η = 0.0315`, where
`D = ⌊n^{1/18}⌋`.  This file has the arithmetic of the proof.  The deduction of the running time
from Theorem 17 that uses it is `Theorem19.explicit_of_theorem_17_corollary_15` and
`Theorem19.explicit_of_theorem_17_corollary_16`, and the theorem about programs is
`wordRam_theorem_19`.

1. Both choices of the parameters, `paramD₅` with `paramG₅` and `paramD₂₆` with `paramG₂₆`, are a
   `Theorem19.Choice` (`Theorem19.choice_theorem_5`, `Theorem19.choice_corollary_26`).  So they
   satisfy the hypotheses of Theorem 17 and of the two corollaries (`Choice.sixteen_le`,
   `Choice.le_n`, `Choice.one_le_ceil`, `Choice.ceil_le_sqrt`, `Choice.pow_eighteen_le`).
2. By the cost analysis for a general choice (`Theorem19.exists_total_le`), the number of instances
   times the cost of one instance, plus the additional time of Theorem 17, is
   `O(n^{3-1/648} log² n)`, respectively `O(n^{3-0.00175} log n)` (`Theorem19.total_theorem_5`,
   `Theorem19.total_corollary_26`).  The step "O(n^{3−ε'} log n) ≤ O(n^{3−ε_T})" of the
   statement is the general fact that a larger exponent absorbs logarithms
   (`IsPowPolylog.isBigOPow`); it is applied in `Theorem19.second_of_explicit`.

NOTE.  "Assume n is larger than a constant depending on ν": the two choices of `D` below are stated
for `n ≥ 16^18`, which makes `D ≥ 16`.

Remark 20 explains the values of `η`: the exponents `η - γ` of the instances and `-η` of the scans
balance at `η = γ/2` (`remark_20_balance`, `remark_20_numbers`), and the straightforward algorithm
for the instances gives back the bound `n³` (`remark_20_brute_force`).
-/

public section

namespace ThreeSumApsp

/-! ### The two choices of the parameters -/













































/-! ### The costs added up -/

























/-! ### Remark 20 -/









































end ThreeSumApsp

end
end

section


/-!
# Theorem 19 from Theorem 17 and Corollaries 15 and 16

Theorem 17 reduces Exact Triangle to `4 n g` calls of Lop-AE-SparseTri plus some extra time.  The
proof of Theorem 19 puts in the cost of one call (Corollary 15 or Corollary 16) and the parameters
`D` and `g`, and adds up.  Both routes have the same three steps:

1. the parameters satisfy the hypotheses of Theorem 17 and of the corollary (`Theorem19.choice_*`);
2. one call, with the reading of its answers, costs `O(I)` (`call_cost_corollary_15` and
   `call_cost_corollary_16`);
3. the sum of all terms is `O(κ P)` (`Theorem19.total_*`, the calculation of the proof of
   Theorem 19).

`time_le_of_calls` puts the three steps together.  The result keeps the dependence on `κ`
(`Claim.Theorem_19_explicit`).  From it follow the two bounds as printed, for every constant `κ`
(`Claim.Theorem_19_explicit.eventually_le`), and a bound for all sizes and all bounds on the
weights, which is what Theorem 21 is applied to (`exactTriangleUniform_of_explicit`): small sizes by
brute force (`dominated_bruteForce`), large sizes by the explicit bound with
`κ = max 1 (log u / log s)` (`dominated_explicit`).
-/

@[expose] public section

namespace ThreeSumApsp







































/-! ## The bounds as printed -/





































/-! ## A bound for all sizes and all bounds on the weights -/
























end ThreeSumApsp

end
end

section


/-!
# Theorem 19 on the word RAM

The route, as in the paper.  Theorem 17 reduces Exact Triangle to instances of the lopsided triangle
problem.  With the parameters `D` and `g` of Section 3.3 and Corollary 15 for the instances the
total is `O(n^{3−1/648} log² n)` (`claim_theorem_19_usingTheorem5`); with Corollary 16 it is
`O(n^{3−ε'} log n)`, `ε' = 0.00175` (`claim_theorem_19_usingCorollary26`).  Both are claims about
programs of the light language that keep the dependence on `κ`.  The outermost procedure for the
input layout and the compiler (`Light.Sec3.realized_exactTriangle`) carry them to the word RAM.
The third bound of the theorem, `O(n^{3−ε_T})`, follows from the second, so it rests on Corollary 16
and not on Corollary 15.

Section 3.4 needs the two bounds for all numbers of vertices and all bounds on the weights:
`claim_exactTriangleUniform_usingTheorem5`, `claim_exactTriangleUniform_usingCorollary26`.  They
combine the program with brute force below a threshold, as in the proof ("smaller instances are
solved by brute force").
-/

public section

open ThreeSumApsp ThreeSumApsp.WordRam

namespace Light.Sec3

















end Light.Sec3

namespace ThreeSumApsp












end ThreeSumApsp

end
end

section


/-!
# APSP: from a solver of the task to a program for the layout of the end statement

APSP (Theorem 22).  `realized_apsp`: if the task `apTask` is solved in time T, then
`EndStatement.APSP` is solved on the word RAM within a constant times T.

The input is n in cell 0, the adjacency matrix from cell 1 and the weights from cell 1 + n².  The
answer goes to the 2n² cells from 1 + 2n², and the free pointer is 1 + 4n² (`apspInst`).  The task
speaks of the graph with weights in `WithTop ℤ` that is read from the two lists, which is the graph
of the instance (`graphOf_apsp`).  So the input meets the task's precondition (`pre_apsp`), and what
a solver leaves in the output cells is what `EndStatement.APSP` asks for (`post_apsp`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.WordRam ThreeSumApsp.Spec

































































































end Light.Sec3

end
end

section


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







































































/-! ## Theorem 22 -/









end ThreeSumApsp

end
end

section


/-!
# Theorem 22 on the word RAM

"Plug Theorem 19 into Theorem 21."  Each bound has three ingredients.

1. The paper's deduction between running times, proved for every reading `M` of the sentence "is
   solved by a deterministic algorithm in time T" (lemmas such as `threeSum_of_uniform_theorem_21a`;
   nothing is assumed about `M`).
2. The reading `lightModel`, in which the sentence means that a program of the light language solves
   the task within T steps.  For this reading the reductions that Theorem 21 cites are theorems,
   because they are written as programs that call an arbitrary solver (`Sec3.claim_…`); so
   Theorem 21 holds for it: `claim_theorem_21a` for 3SUM, `claim_theorem_21b_minPlus` and
   `claim_theorem_21b_apsp` for the (min,+)-product and APSP.
3. The way to the machine: a solver of a task, with one more procedure for the input layout,
   compiled, is a program of the word RAM that takes a constant times as many steps
   (`Sec3.realized_threeSum`, `realized_minPlusProduct`, `realized_apsp`).

From a bound `O(s^{3−δ} (log s)^e)` for Exact Triangle this gives

* 3SUM in `O(n^a)` time for every `a > 2 − δ/2` (`threeSum_of_uniform`);
* the (min,+)-product and APSP in `O(n^{3−δ/3} (log n)^{O(1)})` time (`minPlus_polylog_of_uniform`,
  `apsp_polylog_of_uniform`), and so in `O(n^a)` time for every `a > 3 − δ/3`
  (`SolvedInPolylogTime.solvedInTime`).

The theorem is the case `δ = 1/648` (using Theorem 5) and the case `δ = ε' = 0.00175` (using
Corollary 26).  For 3SUM the programs lose polylogarithmic factors only
(`Theorem22.threeSum_polylog`); the printed form with `n^{o(1)}` follows
(`SolvedInPolylogTime.solvedInLittleOTime`).
-/

public section

open ThreeSumApsp ThreeSumApsp.WordRam

namespace Light.Sec3

/-! ## Theorem 21 for programs of the light language -/










/-! ## A bound for Exact Triangle, plugged into Theorem 21 -/


















end Light.Sec3

namespace ThreeSumApsp





















































end ThreeSumApsp

end
end

section


/-!
# From a real exponent to a rational one

An item statement bounds the steps of a program by `C (n^a + 1)`, with real numbers `C` and `a`.
The end statement uses Lean's core library only.  It asks for a step bound `T` with natural values
that depends on the size alone, and it writes `T(n) = O(n^r)`, for a rational `r = p/q`, as
`T(n)^q ≤ K n^p`.  Here the first bound, rounded up, is shown to be a bound of the second kind
(`bigO_stepBound`), and a program that meets the first is shown to meet the second
(`SolvedInTime.endStatement`).  The program and the slope of the word size stay the same.
-/

public section

namespace ThreeSumApsp.WordRam


































end ThreeSumApsp.WordRam

end
end

section


set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
The three source claims derived directly from the stronger Corollary 26 route.
These proofs avoid projecting from bundled claims that also prove unrelated
3SUM results and weaker bounds. The original source declarations are unchanged.
-/

namespace APSPFocusedSource

open ThreeSumApsp.WordRam


















end APSPFocusedSource





end



end


-- Original source module: ThreeSumApsp.Programs.Sec4.ChoosingParameters.Parameters
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Corollaries 26 and 31 in the light language: rational parameters in the program text

Proof of Corollary 26: "Setting up. Let m := ⌈log₄ D⌉, and pad the inner dimension to 4^m < 4D";
proof of Corollary 31: "with L := ⌈cm⌉ and t := ⌈θm⌉". A program is a finite text, so it can hold c
and θ only if they are rational: c = a/b and θ = p/q (`RatParams`). For real c and θ the statements
follow by approximation (`exists_ratParams`). Corollary 26 is the case c = 21, θ = 1/9, with the
threshold 60 (`ratParams26`).

This file has the parameters, what a structure at the free pointer fr consists of (`structEnd`,
`Ready31`), what the routines ask of the limits (`Lim31`), the query with its specification and its
proof (`QuerySpec31`, `query31_meets`), and the text and the specification of the preprocessing
(`pre31Body`, `PreSpec31`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Parameters -/



variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}










/-- a m ≤ b L. -/
theorem RatParams.am_le (G : RatParams) (m : ℕ) : G.a * m ≤ G.b * G.L m := by
  unfold RatParams.L
  have hb := G.hb
  have hdiv := Nat.div_add_mod (G.a * m + G.b - 1) G.b
  have hmod := Nat.mod_lt (G.a * m + G.b - 1) (by omega : 0 < G.b)
  omega

/-- p m ≤ q m. -/
theorem RatParams.pm_le (G : RatParams) (m : ℕ) : G.p * m ≤ G.q * m :=
  Nat.mul_le_mul_right _ (by have := G.hθ; omega)





































/-! ## The query: the text is query31Body -/









/-! ## The preprocessing: text and interface -/





namespace Pre31
















end Pre31













end Light.Sec4

end

end


-- Original source module: ThreeSumApsp.Util.Counting
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Cardinalities of finite sets

General facts about finite sets.

* A product with one value on `S` and another elsewhere (`Finset.prod_ite_mem_const`); two products
  that vanish unless one set lies in another (`Finset.prod_ite_ite_subset`,
  `Finset.prod_ite_ite_superset`); the number of sets of `k` elements inside a set or around a set
  (`Finset.sum_powersetCard_ite_subset`, `Finset.card_powersetCard_superset`).
* At most `c` elements of a set have a given quotient by `c` under an injective function
  (`Finset.card_filter_div_eq_le`).
* A finite subset of `Fin L` has `j` elements below its `j`-th lowest element
  (`Finset.card_filter_lt_orderEmbOfFin`, from `Finset.card_filter_lt_map` for any increasing
  sequence).

* A function `f : ι → α` has a property `p` at the place `i` if `p (f i)` holds. The number of
  functions `f` with `f i ∈ A i` that have `p` exactly at the places of a set `S` is a product over
  the places (`Finset.card_pi_places_eq`). The number of those that have `p` at exactly `k` places
  is the sum of these products over the sets `S` of `k` places (`Finset.card_pi_places_card`).
  Without the restriction to `A` it is a binomial coefficient times two powers
  (`Finset.card_places_card`).
-/

public section

namespace Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A product that takes the value `a` on `S` and `b` elsewhere. -/
theorem prod_ite_mem_const {M : Type*} [CommMonoid M] (S : Finset ι) (a b : M) :
    (∏ i, if i ∈ S then a else b) = a ^ #S * b ^ (Fintype.card ι - #S) := by
  rw [prod_ite, prod_const, prod_const, filter_mem_eq_inter, univ_inter, filter_not,
    filter_mem_eq_inter, univ_inter, ← compl_eq_univ_sdiff, card_compl]











/-! ## The elements below a bound -/





/-! ## Functions by the set of places with a property -/

variable {α : Type*} [Fintype α]

/-- The number of functions `f` with `f i ∈ A i` whose set of places with `p` is exactly `S`: choose
a value with `p` at each place of `S` and one without `p` at every other place. -/
theorem card_pi_places_eq [DecidableEq α] (A : ι → Finset α) (p : α → Prop) [DecidablePred p]
    (S : Finset ι) :
    #{f : ι → α | (∀ i, f i ∈ A i) ∧ ({i | p (f i)} : Finset ι) = S} =
      ∏ i, if i ∈ S then #{a ∈ A i | p a} else #{a ∈ A i | ¬ p a} := by
  have hmem (i : ι) (x : α) : (x ∈ if i ∈ S then {a ∈ A i | p a} else {a ∈ A i | ¬ p a}) ↔
      x ∈ A i ∧ (p x ↔ i ∈ S) := by
    split_ifs with hi <;> simp [hi]
  simp_rw [← apply_ite Finset.card, ← Fintype.card_piFinset]
  congr 1
  ext f
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, hmem, forall_and,
    Finset.ext_iff]

/-- The number of functions `f` with `f i ∈ A i` that have `p` at exactly `k` places, as a sum over
the possible sets of these places. -/
theorem card_pi_places_card [DecidableEq α] (A : ι → Finset α) (p : α → Prop) [DecidablePred p]
    (k : ℕ) :
    #{f : ι → α | (∀ i, f i ∈ A i) ∧ #{i | p (f i)} = k} =
      ∑ S ∈ powersetCard k (univ : Finset ι),
        ∏ i, if i ∈ S then #{a ∈ A i | p a} else #{a ∈ A i | ¬ p a} := by
  rw [card_eq_sum_card_fiberwise (f := fun f : ι → α => ({i | p (f i)} : Finset ι))
    (t := powersetCard k (univ : Finset ι))
    fun f hf => mem_coe.2 (mem_powersetCard.2 ⟨subset_univ _, (mem_filter.1 hf).2.2⟩)]
  refine sum_congr rfl fun S hS => ?_
  rw [← card_pi_places_eq, filter_filter]
  exact congrArg card (filter_congr fun f _ =>
    ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ (mem_powersetCard.1 hS).2⟩, h.2⟩⟩)

/-- The number of functions `ι → α` that have `p` at exactly `k` places. -/
theorem card_places_card (p : α → Prop) [DecidablePred p] (k : ℕ) :
    #{f : ι → α | #{i | p (f i)} = k} =
      (Fintype.card ι).choose k * (#{a | p a} ^ k * #{a | ¬ p a} ^ (Fintype.card ι - k)) := by
  classical
  have h := card_pi_places_card (ι := ι) (fun _ => (univ : Finset α)) p k
  simp only [mem_univ, implies_true, true_and] at h
  rw [h, sum_congr rfl fun S hS => by
    rw [prod_ite_mem_const, (mem_powersetCard.1 hS).2], sum_const, card_powersetCard, card_univ,
    smul_eq_mul]

end Finset

end

end


-- Original source module: ThreeSumApsp.Sec2.Orders
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


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



/-- One term is `P₀`. -/
private theorem card_term_P0 : (univ.filter fun lam : Term => lam = Term.P0).card = 1 := by decide

/-- Nine terms are different from `P₀`. -/
private theorem card_term_ne_P0 : (univ.filter fun lam : Term => ¬ lam = Term.P0).card = 9 := by
  decide











/-! ### The order of a leaf -/

/-- Membership in the set of levels at which a leaf chooses `P₀`. -/
@[simp]
theorem mem_P0Levels {L : ℕ} {τ : Leaf L} {ℓ : Fin L} : ℓ ∈ P0Levels τ ↔ τ ℓ = Term.P0 := by
  simp [P0Levels]









/-- A leaf has order `d` exactly if it chooses `P₀` at `m - d` levels. -/
theorem order_eq_iff {L : ℕ} (m d : ℕ) (τ : Leaf L) :
    order m τ = d ↔ (P0Levels τ).card + d = m := by
  unfold order
  omega

/-! ### The counts -/





/-- Section 2.4.3: "The total number of leaves of order d in the entire recursion tree is
β_d := binom(L, m-d) 9^{L-m+d}".

NOTE.  `d ≤ m` and `m ≤ L` are left implicit in the paper. -/
theorem card_filter_order_eq {L m : ℕ} (hmL : m ≤ L) (d : ℕ) (hd : d ≤ m) :
    (univ.filter fun τ : Leaf L => order m τ = d).card = beta L m d := by
  -- The leaves of order `d` are the strings of terms with `P₀` at exactly `m - d` levels.
  have hsort : (univ.filter fun τ : Leaf L => order m τ = d)
      = univ.filter fun τ : Leaf L => (univ.filter fun ℓ => τ ℓ = Term.P0).card = m - d := by
    ext τ
    simp only [mem_filter, mem_univ, true_and, order_eq_iff]
    unfold P0Levels
    omega
  rw [hsort, Finset.card_places_card (fun lam : Term => lam = Term.P0) (m - d), card_term_P0,
    card_term_ne_P0, one_pow, one_mul, Fintype.card_fin, beta,
    show L - (m - d) = L - m + d by omega]

/-- Section 2.4.3: "In particular, β₀ = binom(L, m) 9^{L-m}". -/
theorem beta_zero (L m : ℕ) : beta L m 0 = L.choose m * 9 ^ (L - m) := by
  simp [beta]

/-- Section 2.4.3: "β₀ = binom(L, m) 9^{L-m} = M". -/
theorem beta_zero_eq_M (L m : ℕ) : beta L m 0 = M L m := by
  rw [beta_zero, M, K, N0, ← pow_mul, mul_comm (L - m) 2, pow_mul]
  norm_num



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

end


-- Original source module: ThreeSumApsp.Util.Choose
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


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

/-- One summand of the binomial expansion of `(a + b) ^ n` is at most `(a + b) ^ n`. -/
theorem choose_mul_pow_mul_pow_le (a b n k : ℕ) :
    n.choose k * a ^ k * b ^ (n - k) ≤ (a + b) ^ n := by
  obtain hk | hk := le_or_gt k n
  · rw [add_pow]
    calc n.choose k * a ^ k * b ^ (n - k) = a ^ k * b ^ (n - k) * n.choose k := by ring
      _ ≤ _ := Finset.single_le_sum (f := fun k => a ^ k * b ^ (n - k) * n.choose k)
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
  · rw [Nat.choose_eq_zero_of_lt hk, zero_mul, zero_mul]
    exact Nat.zero_le _

/-- `binom(n, k) * b ^ (n - k) ≤ (b + 1) ^ n`. -/
theorem choose_mul_pow_le (b n k : ℕ) : n.choose k * b ^ (n - k) ≤ (b + 1) ^ n := by
  simpa only [one_pow, mul_one, add_comm] using choose_mul_pow_mul_pow_le 1 b n k



/-! ## The largest term of a binomial expansion -/

/-- The term number `j` of the expansion of `n^n = (k + (n-k))^n`. -/
private def modeTerm (n k j : ℕ) : ℕ := n.choose j * k ^ j * (n - k) ^ (n - j)

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

end


-- Original source module: ThreeSumApsp.Sec4.Boxes
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Cubes and boxes (Section 4.2)

A cube is a string of `L` symbols, each of them one of the ten terms or a star, and its leaves are
obtained by replacing each star by any term. A box is a cube with at most `m - t` symbols `P₀` or
stars whose stars are all below its symbols `P₀`. This file proves what the paper says about cubes
and boxes before it turns to the boxes of one output string, in this order:

* from "Notions from Section 2": `M ≤ 10^L` (`M_le_ten_pow`);
* a cube with `e` stars has `10^e` leaves (`Cube.card_leaves`);
* the leaves, the stars and the symbols `P₀` of three cubes: a leaf read as a cube (`Cube.ofLeaf`),
  a cube with a star replaced by a term (`Cube.replace`), and a leaf with stars put at a set of
  levels (`Cube.starAt`); every cube that Section 4.2 makes from a leaf is of this third form;
* the leaves contributing to an output string `η` (w in the paper) are the leaves of the cube of `η`
  (`mem_leaves_cubeOf`), so the entry `(X_Q Y_Q)[η]` is the value of that cube
  (`mul_apply_eq_val_cubeOf`); Section 4.2 starts from this remark, and nothing else rests on it;
* the leaf obtained by replacing the stars of a cube with `P₀` chooses `P₀` where the cube has `P₀`
  or a star (`P0Levels_starsToP0`);
* a box only contains leaves of order at least `t` (`le_order_of_mem_leaves`);
* the `k` lowest levels of a set `S` lie below the other levels of `S` (`lowest_lt`), this property
  characterizes them (`eq_lowest_of_lt`), and there are `min k |S|` of them (`card_lowest`);
* a box is a leaf with its lowest symbols `P₀` replaced by stars (`eq_starLowest_starsToP0`), and
  every cube obtained in this way from a leaf with at most `m - t` symbols `P₀` is a box
  (`isBox_starLowest`).
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

variable {L : ℕ}

/-- Section 4, "Notions from Section 2": "we will use that M = β₀ ≤ 10^L". The equation is
`beta_zero_eq_M`; this is the inequality. -/
theorem M_le_ten_pow (L m : ℕ) : M L m ≤ 10 ^ L := by
  -- `binom(L, m) 9^{L-m}` is one summand of the binomial expansion of `(9 + 1)^L`
  rw [← beta_zero_eq_M, beta_zero]
  exact Nat.choose_mul_pow_le 9 L m

/-! ### Cubes and their leaves (Section 4.2) -/





/-- Membership in the set of star levels of a cube. -/
@[simp]
theorem Cube.mem_starLevels {π : Cube L} {ℓ : Fin L} :
    ℓ ∈ Cube.starLevels π ↔ π ℓ = CubeSymbol.star := by
  simp [Cube.starLevels]

/-- Membership in the set of levels at which a cube has `P₀`. -/
@[simp]
theorem Cube.mem_P0Levels {π : Cube L} {ℓ : Fin L} :
    ℓ ∈ Cube.P0Levels π ↔ π ℓ = CubeSymbol.term Term.P0 := by
  simp [Cube.P0Levels]

/-- No level of a cube has both a star and `P₀`. -/
theorem Cube.disjoint_starLevels_P0Levels (π : Cube L) :
    Disjoint (Cube.starLevels π) (Cube.P0Levels π) := by
  rw [disjoint_left]
  intro ℓ hstar hP0
  rw [Cube.mem_starLevels] at hstar
  rw [Cube.mem_P0Levels, hstar] at hP0
  cases hP0







/-! ### A leaf as a cube without stars (Section 4.2) -/









/-! ### Replacing a star by a term (proof of Lemma 29) -/







/-! ### Putting stars into a leaf (Section 4.2) -/





/-- The stars of `Cube.starAt F τ` are at the levels of `F`. -/
@[simp]
theorem Cube.starLevels_starAt (F : Finset (Fin L)) (τ : Leaf L) :
    Cube.starLevels (Cube.starAt F τ) = F := by
  ext ℓ
  by_cases h : ℓ ∈ F <;> simp [Cube.starAt, h]

/-- The symbols `P₀` of `Cube.starAt F τ` are at the levels outside `F` at which `τ` chooses `P₀`.
-/
@[simp]
theorem Cube.P0Levels_starAt (F : Finset (Fin L)) (τ : Leaf L) :
    Cube.P0Levels (Cube.starAt F τ) = ThreeSumApsp.P0Levels τ \ F := by
  ext ℓ
  by_cases h : ℓ ∈ F <;> simp [Cube.starAt, h]

/-- If `τ` chooses `P₀` at the levels of `F`, then replacing the stars of `Cube.starAt F τ` with
`P₀` gives back `τ`. -/
theorem Cube.starsToP0_starAt {F : Finset (Fin L)} {τ : Leaf L}
    (h : F ⊆ ThreeSumApsp.P0Levels τ) :
    Cube.starsToP0 (Cube.starAt F τ) = τ := by
  funext ℓ
  unfold Cube.starsToP0 Cube.starAt
  split_ifs with hℓ
  · exact (ThreeSumApsp.mem_P0Levels.1 (h hℓ)).symm
  · rfl

/-! ### The cube of an output string (Section 4.2)

Section 4.2 starts from this remark. Nothing else rests on it. -/







/-! ### Replacing the stars of a cube with `P₀` (proof of Lemma 29) -/



/-- A cube is the leaf obtained by replacing its stars with `P₀`, with stars at the star levels of
the cube. -/
theorem Cube.starAt_starLevels_starsToP0 (π : Cube L) :
    Cube.starAt (Cube.starLevels π) (Cube.starsToP0 π) = π := by
  funext ℓ
  unfold Cube.starAt Cube.starsToP0
  cases h : π ℓ <;> simp [h]



/-- The leaf obtained by replacing the stars of a cube with `P₀` chooses `P₀` where the cube has a
star or `P₀`. -/
theorem P0Levels_starsToP0 (π : Cube L) :
    P0Levels (Cube.starsToP0 π) = Cube.starLevels π ∪ Cube.P0Levels π := by
  ext ℓ
  rw [mem_P0Levels, mem_union, Cube.mem_starLevels, Cube.mem_P0Levels]
  unfold Cube.starsToP0
  cases h : π ℓ <;> simp

/-- Proof of Lemma 29: the leaf obtained by replacing the stars of a cube with `P₀` chooses `P₀` at
as many levels as the cube has symbols `P₀` or stars. -/
theorem card_P0Levels_starsToP0 (π : Cube L) :
    (P0Levels (Cube.starsToP0 π)).card = (Cube.starLevels π).card + (Cube.P0Levels π).card := by
  rw [P0Levels_starsToP0, card_union_of_disjoint (Cube.disjoint_starLevels_P0Levels π)]

/-! ### A box only contains leaves of order at least `t` (Section 4.2) -/







/-! ### The `k` lowest levels of a set (Section 4.2) -/

/-- The `k` lowest levels of `S` are levels of `S`. -/
theorem lowest_subset (k : ℕ) (S : Finset (Fin L)) : lowest k S ⊆ S :=
  filter_subset _ _

/-- Membership in the set of the `k` lowest levels of `S`. -/
private lemma mem_lowest {k : ℕ} {S : Finset (Fin L)} {ℓ : Fin L} :
    ℓ ∈ lowest k S ↔ ℓ ∈ S ∧ (S.filter fun ℓ' => ℓ' < ℓ).card < k := by
  simp [lowest]

/-- The number of levels of `S` below a level of `S` grows strictly with the level. -/
private lemma card_below_strictMonoOn (S : Finset (Fin L)) :
    StrictMonoOn (fun ℓ => (S.filter fun x => x < ℓ).card) S := by
  intro ℓ hℓ ℓ' _ hlt
  refine card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · exact mem_filter.2 ⟨(mem_filter.1 hx).1, (mem_filter.1 hx).2.trans hlt⟩
  · exact lt_irrefl ℓ (mem_filter.1 (hsub (mem_filter.2 ⟨hℓ, hlt⟩))).2

/-- Each of the `k` lowest levels of `S` is below every other level of `S`. -/
theorem lowest_lt {k : ℕ} {S : Finset (Fin L)} {ℓ ℓ' : Fin L} (hℓ : ℓ ∈ lowest k S)
    (hℓ' : ℓ' ∈ S \ lowest k S) : ℓ < ℓ' := by
  obtain ⟨hS, hbelow⟩ := mem_lowest.1 hℓ
  obtain ⟨hS', hnot⟩ := mem_sdiff.1 hℓ'
  -- otherwise `ℓ' ≤ ℓ` would have at most as many levels of `S` below it as `ℓ`, fewer than `k`
  by_contra hlt
  exact hnot (mem_lowest.2
    ⟨hS', ((card_below_strictMonoOn S).monotoneOn hS' hS (not_lt.1 hlt)).trans_lt hbelow⟩)

/-- A subset `T` of `S` all of whose levels are below all the other levels of `S` consists of the
`|T|` lowest levels of `S`. -/
theorem eq_lowest_of_lt {S T : Finset (Fin L)} (hT : T ⊆ S)
    (h : ∀ ℓ ∈ T, ∀ ℓ' ∈ S \ T, ℓ < ℓ') : T = lowest T.card S := by
  ext ℓ
  rw [mem_lowest]
  constructor
  · -- The levels of `S` below a level `ℓ` of `T` are levels of `T` other than `ℓ`.
    refine fun hℓ => ⟨hT hℓ, card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩⟩
    · by_contra hxT
      exact lt_asymm (mem_filter.1 hx).2 (h ℓ hℓ x (mem_sdiff.2 ⟨(mem_filter.1 hx).1, hxT⟩))
    · exact lt_irrefl ℓ (mem_filter.1 (hsub hℓ)).2
  · -- All of `T` is below a level of `S` outside `T`.
    rintro ⟨hℓS, hcard⟩
    by_contra hℓT
    refine absurd (card_le_card fun x hx => ?_) (not_le.2 hcard)
    exact mem_filter.2 ⟨hT hx, h x hx ℓ (mem_sdiff.2 ⟨hℓS, hℓT⟩)⟩

/-- The numbers of levels of `S` below the levels of `S` are `0, …, |S| - 1`. -/
private lemma image_card_below (S : Finset (Fin L)) :
    (S.image fun ℓ => (S.filter fun x => x < ℓ).card) = range S.card := by
  refine eq_of_subset_of_card_le (fun n hn => ?_) ?_
  · obtain ⟨ℓ, hℓ, rfl⟩ := mem_image.1 hn
    exact mem_range.2
      (card_lt_card ⟨filter_subset _ _, fun hsub => lt_irrefl ℓ (mem_filter.1 (hsub hℓ)).2⟩)
  · rw [card_image_of_injOn (card_below_strictMonoOn S).injOn, card_range]

/-- The set of the `k` lowest levels of `S` has `min k |S|` elements. -/
theorem card_lowest (k : ℕ) (S : Finset (Fin L)) : (lowest k S).card = min k S.card := by
  -- The map from a level to the number of levels of `S` below it is injective on `S`, its image is
  -- `{0, …, |S| - 1}`, and by definition `lowest k S` is the preimage of the numbers below `k`.
  have hinj := (card_below_strictMonoOn S).injOn.mono (coe_subset.2 (lowest_subset k S))
  have hrange : ((range S.card).filter fun n => n < k) = range (min k S.card) := by
    ext n
    simp only [mem_filter, mem_range, lt_min_iff, and_comm]
  rw [← card_image_of_injOn hinj, ← card_range (min k S.card), ← hrange, ← image_card_below,
    filter_image]
  rfl

/-! ### Replacing the lowest symbols `P₀` of a leaf by stars (Section 4.2 and the proof of Lemma 29)
-/



/-- The stars of `starLowest e τ` are at the `e` lowest levels at which `τ` chooses `P₀`. -/
theorem starLevels_starLowest (e : ℕ) (τ : Leaf L) :
    Cube.starLevels (starLowest e τ) = lowest e (P0Levels τ) :=
  Cube.starLevels_starAt _ τ

/-- The symbols `P₀` of `starLowest e τ` are at the other levels at which `τ` chooses `P₀`. -/
theorem P0Levels_starLowest (e : ℕ) (τ : Leaf L) :
    Cube.P0Levels (starLowest e τ) = P0Levels τ \ lowest e (P0Levels τ) :=
  Cube.P0Levels_starAt _ τ

/-- Replacing the stars of `starLowest e τ` with `P₀` gives back `τ`. -/
theorem starsToP0_starLowest (e : ℕ) (τ : Leaf L) : Cube.starsToP0 (starLowest e τ) = τ :=
  Cube.starsToP0_starAt (lowest_subset _ _)

/-- Section 4.2: "By (ii), a box is obtained from a leaf of order at least t by replacing its e
lowest symbols P₀ (rather than an arbitrary subset of them) by stars." The leaf is
`Cube.starsToP0 π`, and only condition (ii) is used. -/
theorem eq_starLowest_starsToP0 (π : Cube L)
    (h : ∀ ℓ ∈ Cube.starLevels π, ∀ ℓ' ∈ Cube.P0Levels π, ℓ < ℓ') :
    π = starLowest (Cube.starLevels π).card (Cube.starsToP0 π) := by
  have hlow : Cube.starLevels π =
      lowest (Cube.starLevels π).card (P0Levels (Cube.starsToP0 π)) := by
    refine eq_lowest_of_lt ?_ fun ℓ hℓ ℓ' hℓ' => h ℓ hℓ ℓ' ?_
    · rw [P0Levels_starsToP0]
      exact subset_union_left
    · rw [P0Levels_starsToP0, mem_sdiff, mem_union] at hℓ'
      tauto
  rw [starLowest, ← hlow, Cube.starAt_starLevels_starsToP0]

/-- The converse: replacing the `e` lowest symbols `P₀` of a leaf with at most `m - t` symbols `P₀`
by stars gives a box. -/
theorem isBox_starLowest (m t e : ℕ) (τ : Leaf L) (hτ : (P0Levels τ).card ≤ m - t) :
    IsBox m t (starLowest e τ) := by
  rw [IsBox, ← card_P0Levels_starsToP0, starsToP0_starLowest, starLevels_starLowest,
    P0Levels_starLowest]
  exact ⟨hτ, fun ℓ hℓ ℓ' hℓ' => lowest_lt hℓ hℓ'⟩

end ThreeSumApsp

end

end


-- Original source module: ThreeSumApsp.Sec4.Lemma29
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Lemma 29: the number of boxes, and their values (Section 4.3)

*The count* (`lemma_29_count`): there are at most `(m+1) ∑_{d=t}^{m} β_d` boxes. A box with `f`
symbols `P₀` or stars is a leaf with `f` symbols `P₀` in which the `e` lowest of them have been
turned into stars, for some `e ≤ f`. So these boxes correspond to the pairs of such a leaf and a
number `e ≤ f`, there are `(f+1) β_{m-f}` of them (`Lemma29.card_filter`), and we sum over
`f ≤ m - t`.

*The values* (`lemma_29_values`): the dynamic program `dpValue`, run on the two encodings of a tile,
returns the value of every box. This is an induction on the number of stars. The boxes without stars
are leaves (`Lemma29.no_stars`), and their values are products of two encoded numbers
(`Lemma29.val_ofLeaf`). Replacing the highest star of a box by the ten terms gives ten boxes with
one star fewer (`lemma_29_split`), whose values add up to the value of the box
(`Lemma29.recurrence`).
-/

public section

open Finset

namespace ThreeSumApsp

/-- Membership in the set of all boxes. -/
@[simp]
theorem mem_boxes {L m t : ℕ} {π : Cube L} : π ∈ boxes L m t ↔ IsBox m t π := by
  simp [boxes]

/-- Membership in the set of the boxes with `e` stars. -/
@[simp]
theorem mem_boxesWithStars {L m t e : ℕ} {π : Cube L} :
    π ∈ boxesWithStars L m t e ↔ IsBox m t π ∧ (Cube.starLevels π).card = e := by
  simp [boxesWithStars, boxes]

/-! ### The count -/

/-- For `f ≤ m ≤ L`, the number of leaves that choose `P₀` at exactly `f` levels is `β_{m-f}`
(Section 2.4.3). -/
private lemma card_leaves_P0 {L m f : ℕ} (hmL : m ≤ L) (hf : f ≤ m) :
    (univ.filter fun τ : Leaf L => (P0Levels τ).card = f).card = beta L m (m - f) := by
  rw [← card_filter_order_eq hmL (m - f) (Nat.sub_le _ _)]
  congr 1
  ext τ
  rw [mem_filter, mem_filter, order]
  simp only [mem_univ, true_and]
  omega

/-- Proof of Lemma 29, "The count": "There are hence (f+1) binom(L, f) 9^{L-f} = (f+1) β_{m-f} such
boxes", namely boxes with `f` symbols `P₀` or stars, for `f ≤ m - t`. -/
theorem Lemma29.card_filter (L m t f : ℕ) (hmL : m ≤ L) (hf : f ≤ m - t) :
    ((boxes L m t).filter fun π => (Cube.starLevels π).card + (Cube.P0Levels π).card = f).card
      = (f + 1) * beta L m (m - f) := by
  -- The pairs of a leaf with `f` symbols `P₀` and a number `e ≤ f`.
  have hpairs : ((univ.filter fun τ : Leaf L => (P0Levels τ).card = f) ×ˢ range (f + 1)).card
      = (f + 1) * beta L m (m - f) := by
    rw [card_product, card_leaves_P0 hmL (by omega), card_range, mul_comm]
  have hpair : ∀ p ∈ (univ.filter fun τ : Leaf L => (P0Levels τ).card = f) ×ˢ range (f + 1),
      (P0Levels p.1).card = f ∧ p.2 < f + 1 := fun p hp =>
    ⟨(mem_filter.1 (mem_product.1 hp).1).2, mem_range.1 (mem_product.1 hp).2⟩
  -- A box goes to "the leaf we get by replacing its stars with P₀" and the number of its stars;
  -- a pair goes to the cube obtained "by turning the e lowest symbols P₀ of that leaf into stars".
  rw [← hpairs]
  refine card_bij' (fun π _ => (Cube.starsToP0 π, (Cube.starLevels π).card))
    (fun p _ => starLowest p.2 p.1) (fun π hπ => ?_) (fun p hp => ?_) (fun π hπ => ?_)
    fun p hp => ?_
  · -- the pair of such a box is such a pair
    have hf := (mem_filter.1 hπ).2
    simp only [mem_product, mem_filter, mem_univ, true_and, mem_range,
      card_P0Levels_starsToP0]
    omega
  · -- the cube of such a pair is such a box: its leaf is the leaf of the pair
    obtain ⟨hτ, -⟩ := hpair p hp
    rw [mem_filter, mem_boxes, ← card_P0Levels_starsToP0, starsToP0_starLowest]
    exact ⟨isBox_starLowest m t p.2 p.1 (by omega), hτ⟩
  · -- from a box to its pair and back
    exact (eq_starLowest_starsToP0 π (mem_boxes.1 (mem_filter.1 hπ).1).2).symm
  · -- from a pair `(τ, e)` to its cube and back: the cube has `min e f = e` stars
    obtain ⟨hτ, he⟩ := hpair p hp
    rw [starsToP0_starLowest, starLevels_starLowest, card_lowest, hτ,
      min_eq_left (by omega)]

/-- **Lemma 29**, first sentence.  "There are at most (m+1) ∑_{d=t}^{m} β_d boxes." -/
theorem lemma_29_count (L m t : ℕ) (hL : 10 * m ≤ L) (ht : t ≤ m) :
    (boxes L m t).card ≤ (m + 1) * ∑ d ∈ Finset.Icc t m, beta L m d := by
  -- Sort the boxes by the number `f ≤ m - t` of their symbols `P₀` or stars.
  have hsort : (boxes L m t).card = ∑ f ∈ range (m - t + 1),
      ((boxes L m t).filter
        fun π => (Cube.starLevels π).card + (Cube.P0Levels π).card = f).card := by
    refine card_eq_sum_card_fiberwise fun π hπ => ?_
    have hi := (mem_boxes.1 (mem_coe.1 hπ)).1
    simp only [coe_range, Set.mem_Iio]
    omega
  -- The order `d = m - f` runs from `t` to `m`.
  have hreflect : ∑ f ∈ range (m - t + 1), beta L m (m - f) = ∑ d ∈ Finset.Icc t m, beta L m d := by
    rw [range_eq_Ico, sum_Ico_reflect _ _ (by omega)]
    congr 1
    ext d
    simp only [mem_Ico, mem_Icc]
    omega
  -- "summing over f ≤ m - t gives the upper bound on the number of boxes", since `f + 1 ≤ m + 1`
  rw [hsort, ← hreflect, mul_sum]
  refine sum_le_sum fun f hf => ?_
  have hfm : f < m - t + 1 := mem_range.1 hf
  rw [Lemma29.card_filter L m t f (by omega) (by omega)]
  exact Nat.mul_le_mul_right _ (by omega)

/-! ### The values -/











end ThreeSumApsp

end

end


-- Original source module: ThreeSumApsp.Sec4.Theorem30
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


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

/-- Section 4.3: `ρ = 9m/(L-m+1)` "is less than 1 since L ≥ 10m". -/
theorem sec4_rho_lt_one (L m : ℕ) (hL : 10 * m ≤ L) : rho L m < 1 := by
  have hL' : (10 : ℝ) * m ≤ L := by exact_mod_cast hL
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [rho, div_lt_one (by linarith)]
  linarith

/-- The decay rate `ρ` is not negative when `L ≥ 10m`. -/
theorem rho_nonneg {L m : ℕ} (hL : 10 * m ≤ L) : 0 ≤ rho L m := by
  have hL' : (10 : ℝ) * m ≤ L := by exact_mod_cast hL
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  exact div_nonneg (by positivity) (by linarith)

/-- The factor `ρ^t/(1 - ρ)` of (8) is not negative when `L ≥ 10m`. -/
theorem rho_pow_div_nonneg {L m : ℕ} (t : ℕ) (hL : 10 * m ≤ L) :
    0 ≤ rho L m ^ t / (1 - rho L m) :=
  div_nonneg (pow_nonneg (rho_nonneg hL) t) (sub_nonneg.2 (sec4_rho_lt_one L m hL).le)

/-- Equation (7), first half: for `1 ≤ d ≤ m`,
`β_d / β_{d-1} = 9(m-d+1)/(L-m+d) ≤ 9m/(L-m+1) = ρ`. -/
theorem eq_7_ratio (L m d : ℕ) (hL : 10 * m ≤ L) (hd1 : 1 ≤ d) (hdm : d ≤ m) :
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

/-- Equation (7), second half: "so β_d ≤ ρ^d M" (for `0 ≤ d ≤ m`). -/
theorem eq_7 (L m d : ℕ) (hL : 10 * m ≤ L) (hdm : d ≤ m) :
    (beta L m d : ℝ) ≤ rho L m ^ d * (M L m : ℝ) := by
  induction d with
  | zero => simp [beta_zero_eq_M]
  | succ d ih =>
    obtain ⟨hratio, hle⟩ := eq_7_ratio L m (d + 1) hL (by omega) hdm
    have hpos : (0 : ℝ) < (beta L m d : ℝ) := by
      exact_mod_cast beta_pos (L := L) (m := m) (by omega) d
    rw [← hratio, Nat.add_sub_cancel, div_le_iff₀ hpos] at hle
    calc (beta L m (d + 1) : ℝ) ≤ rho L m * (beta L m d : ℝ) := hle
      _ ≤ rho L m * (rho L m ^ d * (M L m : ℝ)) :=
          mul_le_mul_of_nonneg_left (ih (by omega)) (rho_nonneg hL)
      _ = rho L m ^ (d + 1) * (M L m : ℝ) := by ring

/-! ### Theorem 30, "Preprocessing": the count behind (8) -/



/-- `√K N₀` is positive when `m ≤ L`. -/
theorem sqrtKN0_pos {L m : ℕ} (hmL : m ≤ L) : 0 < sqrtKN0 L m := by
  have hK : (0 : ℝ) < (K L m : ℝ) := by exact_mod_cast Nat.choose_pos hmL
  have hN0 : (0 : ℝ) < (N0 L m : ℝ) := by exact_mod_cast N0_pos L m
  exact mul_pos (Real.sqrt_pos.mpr hK) hN0

/-- `(√K N₀)² = K N₀² = M`. -/
theorem sqrtKN0_sq (L m : ℕ) : sqrtKN0 L m ^ 2 = (M L m : ℝ) := by
  rw [sqrtKN0, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp [M]

/-- `√K N₀ ≤ K N₀`, because `K ≥ 1`. -/
theorem sqrtKN0_le {L m : ℕ} (hmL : m ≤ L) : sqrtKN0 L m ≤ (K L m : ℝ) * (N0 L m : ℝ) := by
  have hK : (1 : ℝ) ≤ (K L m : ℝ) := by exact_mod_cast Nat.choose_pos hmL
  exact mul_le_mul_of_nonneg_right
    ((Real.sqrt_le_sqrt (le_self_pow₀ hK two_ne_zero)).trans_eq (Real.sqrt_sq (by positivity)))
    (Nat.cast_nonneg _)

/-- The expression (8), with `√K N₀` under its name. -/
theorem cost8_eq (L m t N : ℕ) :
    cost8 L m t N = (L : ℝ) * (m : ℝ) * (rho L m ^ t / (1 - rho L m)) * (N : ℝ) ^ 2
      + (N : ℝ) * (10 : ℝ) ^ L / sqrtKN0 L m :=
  rfl

/-- The first term of (8) is not negative when `L ≥ 10m`. -/
theorem cost8_first_term_nonneg {L m : ℕ} (t N : ℕ) (hL : 10 * m ≤ L) :
    0 ≤ (L : ℝ) * (m : ℝ) * (rho L m ^ t / (1 - rho L m)) * (N : ℝ) ^ 2 :=
  mul_nonneg (mul_nonneg (by positivity) (rho_pow_div_nonneg t hL)) (by positivity)



/-- Proof of Theorem 30, "Preprocessing": "we store the K₀² subsets, in O(KL) ≤ O(10^L) operations".
Read as the inequality `K L ≤ 10^L` (constant 1). -/
theorem Theorem30.subsets (L m : ℕ) : K L m * L ≤ 10 ^ L := by
  calc K L m * L ≤ 2 ^ L * 2 ^ L :=
        Nat.mul_le_mul (Nat.choose_le_two_pow L m) Nat.lt_two_pow_self.le
    _ = 4 ^ L := by rw [← Nat.mul_pow]
    _ ≤ 10 ^ L := Nat.pow_le_pow_left (by norm_num) L

/-- Proof of Theorem 30, "Preprocessing": the `O(10^L)` operations for the list of subsets, which
are spent once, are within the last term of (8), because `N ≥ √K N₀`. -/
theorem Theorem30.subsets_absorbed {L m N : ℕ} (hL : 10 * m ≤ L) (hN : sqrtKN0 L m ≤ N) :
    (10 : ℝ) ^ L ≤ (N : ℝ) * (10 : ℝ) ^ L / sqrtKN0 L m := by
  rw [le_div_iff₀ (sqrtKN0_pos (by omega)), mul_comm (N : ℝ)]
  exact mul_le_mul_of_nonneg_left hN (by positivity)

/-- `binom(L, r) ≥ L` for `1 ≤ r ≤ L/2`: up to the middle the binomial coefficients increase. -/
private lemma le_choose_of_le_half (L : ℕ) : ∀ r, 1 ≤ r → r ≤ L / 2 → L ≤ L.choose r := by
  intro r h1
  induction r, h1 using Nat.le_induction with
  | base => intro _; simp
  | succ r hr ih =>
    intro h
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- `K₀ ≥ 3` in the range of Theorem 30, because `K = binom(L, m) ≥ L ≥ 10`. -/
private lemma three_le_K0 (L m : ℕ) (hm : 1 ≤ m) (hL : 10 * m ≤ L) : 3 ≤ K0 L m := by
  have hK : L ≤ K L m := le_choose_of_le_half L m hm (by omega)
  exact Nat.le_sqrt.2 (by omega)

/-- The number `b` of row bands, `N/(K₀ N₀)` rounded up, satisfies `b √K N₀ ≤ 2N`. The two bounds of
the paper's proof on the numbers of bands and of tiles rest on this. If `b ≤ 2` it is the hypothesis
`N ≥ √K N₀`. If `b ≥ 3` then `(b - 1) K₀ N₀ < N`, `b ≤ 3(b - 1)/2`, and `√K ≤ K₀ + 1 ≤ 4K₀/3`. -/
theorem Theorem30.numBands_mul_le {L m N : ℕ} (hm : 1 ≤ m) (hL : 10 * m ≤ L)
    (hN : sqrtKN0 L m ≤ N) :
    (numBands L m N : ℝ) * sqrtKN0 L m ≤ 2 * (N : ℝ) := by
  have hN0 : (0 : ℝ) < (N0 L m : ℝ) := by exact_mod_cast N0_pos L m
  have hK0 : (3 : ℝ) ≤ (K0 L m : ℝ) := by exact_mod_cast three_le_K0 L m hm hL
  have hsqrt : Real.sqrt (K L m : ℝ) ≤ (K0 L m : ℝ) + 1 :=
    Real.sqrt_le_iff.2 ⟨by positivity, by exact_mod_cast (Nat.lt_succ_sqrt' (K L m)).le⟩
  have hband : 0 < (K0 L m : ℝ) * (N0 L m : ℝ) := by positivity
  -- `b` is `N/(K₀ N₀)` rounded up
  have hceil : (numBands L m N : ℝ) * ((K0 L m : ℝ) * (N0 L m : ℝ))
      ≤ (N : ℝ) + (K0 L m : ℝ) * (N0 L m : ℝ) := by
    have h : numBands L m N * bandSize L m ≤ N + bandSize L m - 1 := Nat.div_mul_le_self _ _
    have h' : numBands L m N * (K0 L m * N0 L m) ≤ N + K0 L m * N0 L m := by
      unfold bandSize at h
      omega
    exact_mod_cast h'
  rcases Nat.lt_or_ge (numBands L m N) 3 with hb | hb
  · have hb' : (numBands L m N : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_lt_succ hb
    exact (mul_le_mul_of_nonneg_right hb' (sqrtKN0_pos (by omega)).le).trans
      (mul_le_mul_of_nonneg_left hN zero_le_two)
  · have hb' : (3 : ℝ) ≤ (numBands L m N : ℝ) := by exact_mod_cast hb
    have hwide : sqrtKN0 L m ≤ 4 / 3 * ((K0 L m : ℝ) * (N0 L m : ℝ)) := by
      unfold sqrtKN0
      nlinarith [hsqrt, hK0, hN0]
    -- `b √K N₀ ≤ (4b/3) K₀ N₀ ≤ 2 (b - 1) K₀ N₀ ≤ 2N`
    nlinarith [mul_le_mul_of_nonneg_left hwide (by linarith : (0 : ℝ) ≤ (numBands L m N : ℝ)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ (numBands L m N : ℝ) - 3) hband.le, hceil]

/-- Proof of Theorem 30, "Preprocessing": "all row bands and column bands, at most 4N/(√K N₀) of
them". There are `numBands L m N` row bands and as many column bands. Here `N` is the given size,
not the padded one, and the bound comes from `Theorem30.numBands_mul_le`. -/
theorem Theorem30.bands {L m N : ℕ} (hm : 1 ≤ m) (hL : 10 * m ≤ L) (hN : sqrtKN0 L m ≤ N) :
    (2 * numBands L m N : ℝ) ≤ 4 * (N : ℝ) / sqrtKN0 L m := by
  rw [le_div_iff₀ (sqrtKN0_pos (by omega))]
  linarith [Theorem30.numBands_mul_le hm hL hN]

/-- Proof of Theorem 30, "Preprocessing": "K N₀ D ≤ 7^L". This bounds the number of nonzero entries
of the input array of a band, which is why forming it takes `O(L · 7^L)` operations. -/
theorem Theorem30.K_mul_N0_mul_D_le (L m : ℕ) : K L m * N0 L m * D m ≤ 7 ^ L := by
  -- one summand of the binomial expansion of `(4 + 3)^L`
  calc K L m * N0 L m * D m = L.choose m * 4 ^ m * 3 ^ (L - m) := by unfold K N0 D; ring
    _ ≤ 7 ^ L := Nat.choose_mul_pow_mul_pow_le 4 3 L m

/-- Proof of Theorem 30, "Preprocessing": forming the input array of a band takes "O(L · 7^L)
operations", which is within the "O(10^L) operations" of its encoding ("This is the last term of
(8)"). Read as the inequality `L · 7^L ≤ 2 · 10^L`; the constant 1 fails at `L = 3`. From `L = 3`
on, one more level multiplies the left-hand side by `7(L+1)/L ≤ 10`. -/
theorem Theorem30.form_array : ∀ L : ℕ, L * 7 ^ L ≤ 2 * 10 ^ L
  | 0 => by norm_num
  | 1 => by norm_num
  | 2 => by norm_num
  | 3 => by norm_num
  | L + 4 =>
    calc (L + 4) * 7 ^ (L + 4) = (7 * (L + 4)) * 7 ^ (L + 3) := by ring
      _ ≤ (10 * (L + 3)) * 7 ^ (L + 3) := Nat.mul_le_mul_right _ (by omega)
      _ = 10 * ((L + 3) * 7 ^ (L + 3)) := by ring
      _ ≤ 10 * (2 * 10 ^ (L + 3)) := Nat.mul_le_mul_left _ (Theorem30.form_array (L + 3))
      _ = 2 * 10 ^ (L + 4) := by ring

/-- Proof of Theorem 30, "Preprocessing": "the at most 4N²/M tiles, where M = K N₀² is the number of
output entries of a tile". There are `(numBands L m N)²` tiles. Here `N` is the given size, and the
bound comes from `Theorem30.numBands_mul_le`. -/
theorem Theorem30.tiles {L m N : ℕ} (hm : 1 ≤ m) (hL : 10 * m ≤ L) (hN : sqrtKN0 L m ≤ N) :
    ((numBands L m N : ℝ)) ^ 2 ≤ 4 * (N : ℝ) ^ 2 / (M L m : ℝ) := by
  have hpos := sqrtKN0_pos (L := L) (m := m) (by omega)
  rw [← sqrtKN0_sq, le_div_iff₀ (pow_pos hpos 2)]
  calc (numBands L m N : ℝ) ^ 2 * sqrtKN0 L m ^ 2
      = ((numBands L m N : ℝ) * sqrtKN0 L m) ^ 2 := (mul_pow _ _ 2).symm
    _ ≤ (2 * (N : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (Theorem30.numBands_mul_le hm hL hN) 2
    _ = 4 * (N : ℝ) ^ 2 := by ring

/-- Proof of Theorem 30, "Preprocessing": "∑_{d ≥ t} β_d ≤ M ρ^t / (1 - ρ) by (7)". The sum is over
`t ≤ d ≤ m`, as in Lemma 29. -/
theorem Theorem30.sum_beta {L m : ℕ} (t : ℕ) (hL : 10 * m ≤ L) :
    ∑ d ∈ Finset.Icc t m, (beta L m d : ℝ) ≤ (M L m : ℝ) * (rho L m ^ t / (1 - rho L m)) := by
  calc ∑ d ∈ Finset.Icc t m, (beta L m d : ℝ)
      ≤ ∑ d ∈ Finset.Icc t m, rho L m ^ d * (M L m : ℝ) :=
        sum_le_sum fun d hd => eq_7 L m d hL (mem_Icc.mp hd).2
    _ = (M L m : ℝ) * ∑ d ∈ Finset.Ico t (m + 1), rho L m ^ d := by
        rw [← sum_mul, mul_comm, Finset.Ico_add_one_right_eq_Icc]
    _ ≤ (M L m : ℝ) * (rho L m ^ t / (1 - rho L m)) :=
        mul_le_mul_of_nonneg_left
          (geom_sum_Ico_le_of_lt_one (rho_nonneg hL) (sec4_rho_lt_one L m hL))
          (Nat.cast_nonneg _)

/-- Proof of Theorem 30, "Preprocessing", "which gives the first term": the number of boxes of all
tiles together is at most `4 (m+1) ρ^t/(1 - ρ) N²`. -/
theorem Theorem30.boxes_total {L m t N : ℕ} (hm : 1 ≤ m) (hL : 10 * m ≤ L) (ht : t ≤ m)
    (hN : sqrtKN0 L m ≤ N) :
    ((numBands L m N : ℝ)) ^ 2 * ((boxes L m t).card : ℝ)
      ≤ 4 * ((m : ℝ) + 1) * (rho L m ^ t / (1 - rho L m)) * (N : ℝ) ^ 2 := by
  have hM : (0 : ℝ) < M L m := sqrtKN0_sq L m ▸ pow_pos (sqrtKN0_pos (by omega)) 2
  have hdecay := rho_pow_div_nonneg t hL
  -- the boxes of one tile, by Lemma 29 and (7)
  have hboxes : ((boxes L m t).card : ℝ)
      ≤ ((m : ℝ) + 1) * ((M L m : ℝ) * (rho L m ^ t / (1 - rho L m))) :=
    calc ((boxes L m t).card : ℝ) ≤ ((m : ℝ) + 1) * ∑ d ∈ Finset.Icc t m, (beta L m d : ℝ) := by
          exact_mod_cast lemma_29_count L m t hL ht
      _ ≤ ((m : ℝ) + 1) * ((M L m : ℝ) * (rho L m ^ t / (1 - rho L m))) :=
          mul_le_mul_of_nonneg_left (Theorem30.sum_beta t hL) (by positivity)
  -- times the number of tiles; `M` cancels
  calc ((numBands L m N : ℝ)) ^ 2 * ((boxes L m t).card : ℝ)
      ≤ (4 * (N : ℝ) ^ 2 / (M L m : ℝ))
          * (((m : ℝ) + 1) * ((M L m : ℝ) * (rho L m ^ t / (1 - rho L m)))) :=
        mul_le_mul (Theorem30.tiles hm hL hN) hboxes (Nat.cast_nonneg _) (by positivity)
    _ = 4 * ((m : ℝ) + 1) * (rho L m ^ t / (1 - rho L m)) * (N : ℝ) ^ 2 := by
        field_simp

/-- The first term of (8): `L` operations for each box of each tile. -/
theorem Theorem30.boxes_cost {L m t N : ℕ} (hm : 1 ≤ m) (hL : 10 * m ≤ L) (ht : t ≤ m)
    (hN : sqrtKN0 L m ≤ N) :
    (L : ℝ) * ((numBands L m N : ℝ) ^ 2 * ((boxes L m t).card : ℝ))
      ≤ 8 * ((L : ℝ) * (m : ℝ) * (rho L m ^ t / (1 - rho L m)) * (N : ℝ) ^ 2) := by
  have hdecay := rho_pow_div_nonneg t hL
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  calc (L : ℝ) * ((numBands L m N : ℝ) ^ 2 * ((boxes L m t).card : ℝ))
      ≤ (L : ℝ) * (4 * ((m : ℝ) + 1) * (rho L m ^ t / (1 - rho L m)) * (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (Theorem30.boxes_total hm hL ht hN) (Nat.cast_nonneg L)
    _ ≤ (L : ℝ) * (4 * (2 * (m : ℝ)) * (rho L m ^ t / (1 - rho L m)) * (N : ℝ) ^ 2) := by
        -- `m + 1 ≤ 2m`
        gcongr
        linarith
    _ = 8 * ((L : ℝ) * (m : ℝ) * (rho L m ^ t / (1 - rho L m)) * (N : ℝ) ^ 2) := by ring

/-- The last term of (8): `10^L + L · 7^L` operations for each row band and each column band. -/
theorem Theorem30.bands_cost {L m N : ℕ} (hm : 1 ≤ m) (hL : 10 * m ≤ L) (hN : sqrtKN0 L m ≤ N) :
    2 * (numBands L m N : ℝ) * ((10 : ℝ) ^ L + (L : ℝ) * (7 : ℝ) ^ L)
      ≤ 12 * ((N : ℝ) * (10 : ℝ) ^ L / sqrtKN0 L m) := by
  have hpos := sqrtKN0_pos (L := L) (m := m) (by omega)
  have hform : (L : ℝ) * (7 : ℝ) ^ L ≤ 2 * (10 : ℝ) ^ L := by
    exact_mod_cast Theorem30.form_array L
  calc 2 * (numBands L m N : ℝ) * ((10 : ℝ) ^ L + (L : ℝ) * (7 : ℝ) ^ L)
      ≤ (4 * (N : ℝ) / sqrtKN0 L m) * (3 * (10 : ℝ) ^ L) :=
        mul_le_mul (Theorem30.bands hm hL hN) (by linarith) (by positivity) (by positivity)
    _ = 12 * ((N : ℝ) * (10 : ℝ) ^ L / sqrtKN0 L m) := by ring

/-- **Theorem 30**, expression (8), as a count: the three parts of the preprocessing added up. `L`
operations for each box of each tile, `10^L + L · 7^L` for each row band and column band, and `K L`
for the list of subsets, are together at most 13 times the expression inside the `O(·)` of (8). The
count uses the hypotheses `m ≥ 1` (for `m + 1 ≤ 2m`, and for the numbers of bands and of tiles) and
`N ≥ √K N₀` of Theorem 30. -/
theorem Theorem30.cost8_assembly {L m t N : ℕ} (hm : 1 ≤ m) (hL : 10 * m ≤ L) (ht : t ≤ m)
    (hN : sqrtKN0 L m ≤ N) :
    (L : ℝ) * ((numBands L m N : ℝ) ^ 2 * ((boxes L m t).card : ℝ))
        + 2 * (numBands L m N : ℝ) * ((10 : ℝ) ^ L + (L : ℝ) * (7 : ℝ) ^ L) + (K L m : ℝ) * (L : ℝ)
      ≤ 13 * cost8 L m t N := by
  have hboxes := Theorem30.boxes_cost hm hL ht hN
  have hbands := Theorem30.bands_cost hm hL hN
  have htable : (K L m : ℝ) * (L : ℝ) ≤ (N : ℝ) * (10 : ℝ) ^ L / sqrtKN0 L m :=
    le_trans (by exact_mod_cast Theorem30.subsets L m) (Theorem30.subsets_absorbed hL hN)
  -- 8 times the first term of (8) and 12 + 1 times the second, and neither is negative
  have hfirst := cost8_first_term_nonneg t N hL
  have hlast := (pow_nonneg (by norm_num : (0 : ℝ) ≤ 10) L).trans
    (Theorem30.subsets_absorbed hL hN)
  rw [cost8_eq]
  linarith

/-! ### Theorem 30, "Query": a query returns `(XY)[I, J]` -/













/-! ### Theorem 30, "Word size" -/



end ThreeSumApsp

end

end


-- Original source module: ThreeSumApsp.Spec.Sec4.Theorem30.NineStrings
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Strings of digits with a bounded number of nines (Section 4.2, proofs of Lemma 29, Theorem 30)

All three enumerations of Section 4 come from one: `nineStrs n lo hi`, the strings of n digits
0, …, 9 in which the digit 9 (the digit of P₀) occurs at least lo and at most hi times, in
lexicographic order.

* The boxes with e stars are the leaves with between e and m - t symbols P₀, with their e lowest
  symbols P₀ turned into stars (the proof of Lemma 29).
* The leaves of order below t contributing to an output string η (the paper's w) have, at the m
  levels of its inner set Q, a string with at least m - t + 1 nines (proof of Theorem 30).
* The boxes of η have, at the m levels of Q, a string with exactly m - t nines, the nines being the
  levels of V (Section 4.2).

The file proves what the list contains (`mem_nineStrs`), that it is increasing
(`pairwise_lt_nineStrs`), how long it is (`length_nineStrs`: ∑_f binom(n, f) 9^{n-f}), and how a
routine goes through it: it starts with `nineFirst` (`head?_nineStrs`), and `nineNext` goes from
each string to the next (`nineNext_getElem`); so the string reached after i steps,
`nineStr n lo hi i`, is the member number i (`getElem_nineStrs`).  Read from the right end of the
string, `nineNext` is one pass: skip the positions that cannot be raised, raise one digit
(`nineRaise`), and fill the rest with the least admissible string, zeros followed by nines.  The
proof follows the recursion of the list: the strings with the first digit d form a block,
`nineNext` goes through each block (`nextTo_map_cons`), and from the last string of a block to the
first string of the next block (`head_nineBlocks`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec











/-! ## The members of the list -/

/-- The first digit is below 9, or it is a 9 and counts. -/
private theorem cons_mem_nineStrs {n lo hi d : ℕ} {l : List ℕ} :
    d :: l ∈ nineStrs (n + 1) lo hi ↔
      (d < 9 ∧ l ∈ nineStrs n lo hi) ∨ (d = 9 ∧ hi ≠ 0 ∧ l ∈ nineStrs n (lo - 1) (hi - 1)) := by
  rw [nineStrs, List.mem_append, List.mem_flatMap]
  refine or_congr ?_ ?_
  · simp only [List.mem_range, List.mem_map, List.cons.injEq]
    exact ⟨fun ⟨a, ha, l', hl', had, hll⟩ => ⟨had ▸ ha, hll ▸ hl'⟩,
      fun ⟨hd, hl⟩ => ⟨d, hd, l, hl, rfl, rfl⟩⟩
  · by_cases hhi : hi = 0
    · simp [hhi]
    · simp only [if_neg hhi, List.mem_map, List.cons.injEq]
      exact ⟨fun ⟨l', hl', hd, hll⟩ => ⟨hd.symm, hhi, hll ▸ hl'⟩,
        fun ⟨hd, _, hl⟩ => ⟨l, hl, hd.symm, rfl⟩⟩

theorem mem_nineStrs {n lo hi : ℕ} (l : List ℕ) :
    l ∈ nineStrs n lo hi ↔
      l.length = n ∧ (∀ d ∈ l, d < 10) ∧ lo ≤ l.count 9 ∧ l.count 9 ≤ hi := by
  induction n generalizing lo hi l with
  | zero => cases l <;> by_cases h : lo = 0 <;> simp [nineStrs, h]
  | succ n ih =>
    rcases l with _ | ⟨d, l⟩
    · simp [nineStrs]
    rw [cons_mem_nineStrs, ih, ih, List.length_cons, List.forall_mem_cons,
      Nat.add_right_cancel_iff]
    by_cases hd : d = 9
    · -- a nine less is needed, and a nine less is allowed, in the rest
      subst hd
      rw [List.count_cons_self]
      grind
    · rw [List.count_cons_of_ne hd]
      grind



/-- The digit of the star does not occur. -/
theorem ten_notMem_of_mem_nineStrs {n lo hi : ℕ} {l : List ℕ} (hl : l ∈ nineStrs n lo hi) :
    10 ∉ l :=
  fun h => absurd (((mem_nineStrs l).1 hl).2.1 10 h) (lt_irrefl 10)

/-- There is no string with more nines than digits, or if the bounds contradict each other. -/
private theorem nineStrs_eq_nil {n lo hi : ℕ} (h : n < lo ∨ hi < lo) : nineStrs n lo hi = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro l hl
  obtain ⟨hlen, -, hlo, hhi⟩ := (mem_nineStrs l).1 hl
  have hcount := List.count_le_length (a := 9) (l := l)
  omega

/-- The list is strictly increasing in the lexicographic order. -/
theorem pairwise_lt_nineStrs (n lo hi : ℕ) : (nineStrs n lo hi).Pairwise (· < ·) := by
  induction n generalizing lo hi with
  | zero =>
    rw [nineStrs]
    split_ifs <;> simp
  | succ n ih =>
    rw [nineStrs, List.pairwise_append, List.pairwise_flatMap]
    refine ⟨⟨fun d _ => ?_, ?_⟩, ?_, ?_⟩
    · rw [List.pairwise_map]
      exact (ih lo hi).imp fun h => List.cons_lt_cons_iff.2 (Or.inr ⟨rfl, h⟩)
    · refine List.pairwise_lt_range.imp fun {a b} hab x hx y hy => ?_
      obtain ⟨x', -, rfl⟩ := List.mem_map.1 hx
      obtain ⟨y', -, rfl⟩ := List.mem_map.1 hy
      exact List.cons_lt_cons_iff.2 (Or.inl hab)
    · split_ifs
      · simp
      · rw [List.pairwise_map]
        exact (ih _ _).imp fun h => List.cons_lt_cons_iff.2 (Or.inr ⟨rfl, h⟩)
    · intro x hx y hy
      obtain ⟨d, hd, hx⟩ := List.mem_flatMap.1 hx
      obtain ⟨x', -, rfl⟩ := List.mem_map.1 hx
      split_ifs at hy
      · simp at hy
      · obtain ⟨y', -, rfl⟩ := List.mem_map.1 hy
        exact List.cons_lt_cons_iff.2 (Or.inl (List.mem_range.1 hd))

theorem nineStrs_nodup (n lo hi : ℕ) : (nineStrs n lo hi).Nodup :=
  (pairwise_lt_nineStrs n lo hi).imp fun h => ne_of_lt h

/-! ## The length of the list -/

/-- The recursion for the length of the list. -/
private theorem length_nineStrs_succ (n lo hi : ℕ) :
    (nineStrs (n + 1) lo hi).length = 9 * (nineStrs n lo hi).length
      + if hi = 0 then 0 else (nineStrs n (lo - 1) (hi - 1)).length := by
  rw [nineStrs, List.length_append, List.length_flatMap]
  congr 1
  · simp only [List.length_map, List.map_const', List.length_range, List.sum_replicate_nat]
  · split_ifs <;> simp

/-- Strings without a nine: one more digit, nine times as many. -/
private theorem nineTerm_zero (n : ℕ) :
    (n + 1).choose 0 * 9 ^ (n + 1 - 0) = 9 * (n.choose 0 * 9 ^ (n - 0)) := by
  simp [pow_succ, mul_comm]

/-- Strings with g + 1 nines: the first digit is a nine or one of the nine other digits. -/
private theorem nineTerm_succ (n g : ℕ) :
    (n + 1).choose (g + 1) * 9 ^ (n + 1 - (g + 1))
      = n.choose g * 9 ^ (n - g) + 9 * (n.choose (g + 1) * 9 ^ (n - (g + 1))) := by
  rw [Nat.choose_succ_succ, Nat.add_sub_add_right, add_mul]
  congr 1
  rcases Nat.lt_or_ge n (g + 1) with h | h
  · rw [Nat.choose_eq_zero_of_lt h]
    simp
  · rw [show n - g = n - (g + 1) + 1 by omega, pow_succ]
    ring

/-- A sum from 0: the first summand apart. -/
private theorem sum_Icc_zero_succ (h : ℕ) (G : ℕ → ℕ) :
    ∑ f ∈ Finset.Icc 0 (h + 1), G f = G 0 + ∑ g ∈ Finset.Icc 0 h, G (g + 1) := by
  rw [← Nat.range_succ_eq_Icc_zero, ← Nat.range_succ_eq_Icc_zero, Finset.sum_range_succ', add_comm]

/-- A sum with both ends shifted by one. -/
private theorem sum_Icc_succ_succ (l h : ℕ) (G : ℕ → ℕ) :
    ∑ f ∈ Finset.Icc (l + 1) (h + 1), G f = ∑ g ∈ Finset.Icc l h, G (g + 1) := by
  rw [← Finset.map_add_right_Icc, Finset.sum_map]
  rfl

/-- There are binom(n, f) 9^{n-f} strings with exactly f nines. -/
theorem length_nineStrs (n lo hi : ℕ) :
    (nineStrs n lo hi).length = ∑ f ∈ Finset.Icc lo hi, n.choose f * 9 ^ (n - f) := by
  induction n generalizing lo hi with
  | zero =>
    rw [nineStrs]
    split_ifs with h
    · subst h
      rw [Finset.sum_eq_single_of_mem 0 (by simp) fun b _ hb => by
        rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hb), zero_mul]]
      rfl
    · refine (Finset.sum_eq_zero fun f hf => ?_).symm
      have := (Finset.mem_Icc.1 hf).1
      rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
  | succ n ih =>
    rw [length_nineStrs_succ, ih]
    rcases hi with _ | h
    · -- no nine is allowed
      rw [if_pos rfl, add_zero, Finset.mul_sum]
      refine Finset.sum_congr rfl fun f hf => ?_
      obtain rfl : f = 0 := Nat.le_zero.mp (Finset.mem_Icc.1 hf).2
      exact (nineTerm_zero n).symm
    · rw [if_neg (Nat.succ_ne_zero h), ih, Nat.add_sub_cancel]
      rcases lo with _ | l
      · rw [sum_Icc_zero_succ, sum_Icc_zero_succ, nineTerm_zero, Nat.zero_sub, mul_add,
          Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
        refine congrArg _ (Finset.sum_congr rfl fun g _ => ?_)
        rw [nineTerm_succ, add_comm]
      · rw [sum_Icc_succ_succ, sum_Icc_succ_succ, Nat.add_sub_cancel, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [nineTerm_succ, add_comm]

/-! ## The first string -/



/-- The least string begins with 0 if not all digits have to be nines. -/
private theorem nineFirst_succ {n lo : ℕ} (h : lo ≤ n) :
    nineFirst (n + 1) lo = 0 :: nineFirst n lo := by
  rw [nineFirst, nineFirst, Nat.succ_sub h, List.replicate_succ, List.cons_append]

/-- The string of nines. -/
private theorem nineFirst_self_succ (n : ℕ) : nineFirst (n + 1) (n + 1) = 9 :: nineFirst n n := by
  simp [nineFirst, List.replicate_succ]

/-- Without strings of n digits there are no strings of n + 1 digits that begin below 9. -/
private theorem flatMap_map_nil (l : List ℕ) :
    l.flatMap (fun d => ([] : List (List ℕ)).map (d :: ·)) = [] :=
  List.flatMap_eq_nil_iff.2 fun _ _ => rfl

theorem head?_nineStrs {n lo hi : ℕ} (h : lo ≤ n) (h' : lo ≤ hi) :
    (nineStrs n lo hi).head? = some (nineFirst n lo) := by
  induction n generalizing lo hi with
  | zero =>
    obtain rfl : lo = 0 := by omega
    rfl
  | succ n ih =>
    rw [nineStrs]
    rcases Nat.lt_or_ge n lo with hlo | hlo
    · -- all digits are nines
      obtain rfl : lo = n + 1 := by omega
      rw [nineStrs_eq_nil (Or.inl (Nat.lt_succ_self n)), if_neg (by omega), flatMap_map_nil,
        List.nil_append, List.head?_map, Nat.add_sub_cancel, ih le_rfl (by omega),
        nineFirst_self_succ]
      rfl
    · rw [List.range_succ_eq_map, List.flatMap_cons, List.append_assoc, List.head?_append,
        List.head?_map, ih hlo h', nineFirst_succ hlo]
      rfl

/-! ## From each string to the next -/











section

variable {n lo hi : ℕ}







end





section

variable {n lo hi i : ℕ}











end

end ThreeSumApsp.Spec

end

end


-- Original source module: ThreeSumApsp.Spec.Sec4.Theorem30.QueryLists
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# What a query reads (proof of Theorem 30, "Query")

The output string, which the paper calls w, is η as a string of variables and w as the list of its
digits; the levels of its inner set Q are the positions of the digit 9.  w is also the list of
digits of the private leaf of η, and `scatter w s` replaces its m nines by a string s of m digits:
the paper's "forming its leaf or its box from the private leaf".  A query adds up the products at
the leaves of order below t contributing to η, and the stored values of the boxes of η (steps (2)
and (3) of the query in Section 4.3).

* `lowList`: the strings with at least m - t + 1 nines give the leaves of order below t ("Each of
  these leaves is obtained from the private leaf of w, which has P₀ at every level of Q, by picking
  fewer than t of those levels and replacing P₀ with one of the nine other terms at each of them");
* `boxesOf`: the strings with exactly m - t nines give the leaves of order exactly t, and `starRun`
  turns the leading nines into stars.  This is the second description of the boxes of w in
  Section 4.2: "For such a leaf, consider the lowest level of Q at which it chooses a term other
  than P₀, and replace its P₀ by a star at every lower level of Q (or at every level of Q, if
  t = 0).  The result is a box of w, and each box of w arises exactly once in this way".  On cubes
  the result is `starBelow`, and the members of the list are exactly the strings of the cubes
  `starBelow η τ` for these leaves τ (`mem_boxesOf_iff`; no other proof rests on this statement).
  In the first description the nines are the levels of V, and the leading nines those of F_V, which
  "is the longest initial segment of Q contained in V".  `starRunIf` is `starRun` as a pass over the
  string with one flag.

The results are `sum_lowList` and `sum_boxesOf` (a sum over one of the lists is the sum over the set
of the paper) and `sum_queryTerms_storedD` (the numbers that a query adds up have the sum of the
query of the paper). Each list is compared with its set by counting
(`List.sum_map_eq_sum_of_length_eq_card`):
1. The list has no repetitions: `scatter w` is injective on strings of m digits, and `starRun` can
   be undone (`lowList_nodup`, `boxesOf_nodup`).
2. Each member is the list of digits of a member of the set.  `scatter w s` is a leaf τ contributing
   to η with as many symbols P₀ as s has nines (`exists_leaf_scatter`).  With at least m - t + 1
   nines its order is below t (`exists_of_mem_lowList`).  With exactly m - t nines its order is t.
   The cube `starBelow η τ` has the digits of τ with stars at the levels of F_Z, where Z, the set
   of the levels of Q at which τ chooses P₀, is the nines of s.  `Unreached` is the formula for F_Z
   read on digits (`unreached_iff_mem_FV`); it holds exactly at the leading nines of s
   (`getD_scatter_starRun`), so the cube has the digits `scatter w (starRun s)`
   (`digitsC_starBelow`, `exists_leaf_of_mem_boxesOf`), and it is a box of η (`starBelow_mem`,
   `exists_of_mem_boxesOf`).
3. The lists have ∑_{d<t} α_d and α_t members (`length_lowList`, `length_boxesOf`), and so have the
   sets, by the last line of Lemma 28 (`lemma_28_counts`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec











/-! ## Putting a string at the positions of the nines -/

















/-! ## The leading nines turned into stars -/



















/-! ## The leaves of order below t -/

section

variable {L m t : ℕ} {η : OutStr L}









/-- There are ∑_{d < t} α_d such leaves. -/
theorem length_lowList (ht : t ≤ m) (w : List ℕ) :
    (lowList m t w).length = ∑ d ∈ Finset.range t, alpha m d := by
  rw [lowList, List.length_map, length_nineStrs]
  -- a string with f nines gives a leaf of order d = m - f: reflect the sum
  refine Finset.sum_nbij' (fun f => m - f) (fun d => m - d) ?_ ?_ ?_ ?_
    fun f hf => by rw [alpha, Nat.choose_symm (Finset.mem_Icc.mp hf).2]
  all_goals
    simp only [Finset.mem_Icc, Finset.mem_range]
    intro a ha
    omega



/-! ## The boxes -/











/-- "This means that w has exactly α_t boxes." -/
theorem length_boxesOf (ht : t ≤ m) (w : List ℕ) : (boxesOf m t w).length = alpha m t := by
  rw [boxesOf, List.length_map, length_nineStrs, Finset.Icc_self, Finset.sum_singleton, alpha,
    Nat.choose_symm ht, Nat.sub_sub_self ht]





end

/-! ## The query -/



end ThreeSumApsp.Spec

end

end


-- Original source module: ThreeSumApsp.Util.Digits
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Strings of digits as numbers

The paper indexes its arrays by strings (Section 2.3.1).  A program indexes them by numbers: the
string `d₁ d₂ ⋯ d_n` of digits in base `b` is coded by the number `d₁ b^{n-1} + ⋯ + d_n`.  The first
digit (the paper's level 1) is the most significant one, so the strings that begin with a given
digit have consecutive codes, and a slice of an array is a contiguous part of it.

* `code` is the number of a string, `digit` reads one digit of a number, `digitList` all of them,
  and `ofDigitList` is Horner's rule.
* `code` and `digit` undo each other (`digit_code`, `code_digit`), so the strings of length `n`
  correspond to the numbers below `b^n` (`codeEquiv`).
* For lists of digits, `digitList` undoes `ofDigitList` (`digitList_ofDigitList`). A list of `n`
  digits has a value below `b^n` (`ofDigitList_lt`), which determines it (`eq_of_ofDigitList_eq`).
  One more digit at the end is one more step of Horner's rule (`ofDigitList_append_singleton`,
  `ofDigitList_take_succ`).
* For an alphabet `α` whose letters are numbered by `e : α ≃ Fin b`, `codeStr e` and `decodeStr e`
  go from strings over `α` to numbers and back, so these strings, too, correspond to the numbers
  below `b^n` (`strEquiv`).  `digitsStr e` is the list of the digits of such a string; Horner's rule
  computes the code from it (`ofDigitList_digitsStr`).

Mathlib's `Nat.ofDigits` and `finFunctionFinEquiv` put the least significant digit first, so they
would make a slice a scattered part of an array; this is why the codes are defined here.
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## Strings of numbers below `b` -/

































/-! ## Lists of digits -/























/-! ## Strings over a numbered alphabet -/

variable {α : Type} {b : ℕ} (e : α ≃ Fin b)





















/-! ## The list of the digits of a string -/



section

variable {α : Type} {b : ℕ} (e : α ≃ Fin b) {n : ℕ}

theorem length_digitsStr (u : Fin n → α) : (digitsStr e u).length = n := List.length_ofFn

theorem digitsStr_lt (u : Fin n → α) : ∀ d ∈ digitsStr e u, d < b := by
  intro d hd
  obtain ⟨ℓ, rfl⟩ := List.mem_ofFn.mp hd
  exact (e _).isLt

theorem digitsStr_injective : Function.Injective (digitsStr e : (Fin n → α) → List ℕ) :=
  fun _ _ h => funext fun ℓ => e.injective (Fin.ext (congrFun (List.ofFn_injective h) ℓ))

/-- Every list of n digits below b is the list of digits of a string. -/
theorem exists_digitsStr (l : List ℕ) (hl : l.length = n) (hd : ∀ d ∈ l, d < b) :
    ∃ u : Fin n → α, digitsStr e u = l := by
  subst hl
  refine ⟨fun ℓ => e.symm ⟨l[ℓ], hd _ (List.getElem_mem _)⟩, ?_⟩
  simp only [digitsStr, Equiv.apply_symm_apply]
  exact List.ofFn_getElem

/-- The digit at a level. -/
theorem getD_digitsStr (u : Fin n → α) (ℓ : Fin n) : (digitsStr e u).getD ℓ 0 = e (u ℓ) := by
  simp [digitsStr, List.getD_eq_getElem?_getD]

/-- A list with n members and the right digit at every level is the list of digits of the
string. -/
theorem digitsStr_eq_of_getD (u : Fin n → α) {l : List ℕ} (hl : l.length = n)
    (h : ∀ ℓ : Fin n, l.getD ℓ 0 = e (u ℓ)) : digitsStr e u = l := by
  refine List.ext_getElem (by rw [length_digitsStr, hl]) fun i hi _ => ?_
  rw [length_digitsStr] at hi
  rw [← List.getD_eq_getElem l 0, h ⟨i, hi⟩]
  simp only [digitsStr, List.getElem_ofFn]





end

end ThreeSumApsp

end

end


-- Original source module: ThreeSumApsp.Util.List
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Lists: entries with a default, blocks, sums, counting, sorted lists

General facts about lists. Arrays are lists here, and entry `i` of a list is `l.getD i d`. The
sections:

* Entries with a default: `getD` of a list that was appended to, cut, tabulated, mapped or changed
  in one place.
* Blocks: `(List.range n).flatMap f` puts the blocks `f 0, …, f (n - 1)` one after the other. Where
  an entry of a block stands, for blocks of any lengths and for blocks of one length.
* Sums: partial sums, the triangle inequality, and the sum over a list that enumerates the image of
  a finite set.
* A running minimum.
* Counting: how often a value occurs among the first entries of a list, or among the values of a
  function on `Fin n`; the list of the `j < n` with a property.
* Sorted lists: what `dropWhile` and `takeWhile` leave of a strictly increasing list; first
  occurrences in a weakly increasing list.
* Two notions of this project: `AbsLe l U` says that all members of `l` have absolute value at most
  `U`, and `sumLists` is the entrywise sum of lists of one length.
-/

@[expose] public section

namespace List

variable {α β : Type*}

/-! ## Entries with a default -/



















/-! ## Blocks one after the other -/

















/-! ## Sums -/

/-- The sum of the table `f 0, …, f (n - 1)` is the sum over `Finset.range n`. For a sum over
`Fin n` go on with `Finset.sum_range`. -/
theorem sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i :=
  rfl











section

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]





end









/-! ## A running minimum -/





/-! ## Counting -/













/-- How often a value occurs among the first `i` values of a function on `Fin n`. -/
theorem count_take_ofFn [DecidableEq α] {n : ℕ} (f : Fin n → α) (a : α) (i : ℕ) :
    ((List.ofFn f).take i).count a =
      (Finset.univ.filter fun j : Fin n => (j : ℕ) < i ∧ f j = a).card := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    cases i with
    | zero => simp
    | succ i =>
      rw [List.ofFn_succ, List.take_succ_cons, List.count_cons, ih, Finset.card_filter,
        Finset.card_filter, Fin.sum_univ_succ, add_comm]
      simp

/-- How often a value occurs in the table of a function on `Fin n`. -/
theorem count_ofFn [DecidableEq α] {n : ℕ} (f : Fin n → α) (a : α) :
    (List.ofFn f).count a = (Finset.univ.filter fun i => f i = a).card := by
  simpa [List.take_of_length_le] using count_take_ofFn f a n

/-! ## Sorted lists -/

section Sorted

variable [LinearOrder α]







end Sorted

end List

namespace ThreeSumApsp

variable {α β : Type*}

/-! ## Lists of integers that are bounded in absolute value -/









/-! ## The entrywise sum of lists -/





end ThreeSumApsp

end

end


-- Original source module: ThreeSumApsp.Spec.Sec4.Theorem30.Cubes
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Cubes, leaves and output strings as lists of digits (Sections 4.2 and 4.3)

A term has the digit P_ij ↦ 3(i - 1) + (j - 1), P₀ ↦ 9, and an output variable the digit
z_ij ↦ 3(i - 1) + (j - 1), z₀ ↦ 9.  A symbol of a cube that is a term keeps the digit of the term,
and the star has the digit 10.  A cube, a leaf or an output string is handled as the list of its L
digits, level 1 first: `digitsC` for cubes, `digitsT` for strings of terms (leaves), `digitsO` for
output strings.  This file translates the notions of Sections 4.2 and 4.3 into operations on such
lists:

* the inner set of an output string η (the paper's w) is the positions of its digit 9, the stars of
  π are the positions of 10, the symbols P₀ of τ the positions of 9, and their numbers are counts
  (`card_innerSetO`, `card_starLevels`, `card_P0Levels`);
* "replacing its e lowest symbols P₀ […] by stars" is `starFirst` (`digitsC_starLowest`);
* "replacing its stars with P₀" is `starsToNines` (`digitsT_starsToP0`);
* "the highest level at which π has a star" is `lastStar` (`lastStar_digitsC`), and π[ℓ ← λ] is
  `List.set` (`digitsC_replace`);
* the dynamic program of Lemma 29 is `dpValueD` (`dpValueD_digitsC`): the product `leafProduct` for
  a list without stars, and the step `sumAtLastStar`; `storedD` is what it computes for a box, at
  the number of stars of the box.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Cubes, leaves and output strings -/











section

variable {L : ℕ} (π : Cube L) (τ : Leaf L) (η : OutStr L)


theorem length_digitsT : (digitsT τ).length = L := length_digitsStr _ τ



theorem digitsT_lt : ∀ d ∈ digitsT τ, d < 10 := digitsStr_lt _ τ



theorem getD_digitsT (ℓ : Fin L) : (digitsT τ).getD ℓ 0 = termIdx (τ ℓ) := getD_digitsStr _ τ ℓ


/-- A list with L members and the right digit at every level is the list of digits of the cube. -/
theorem digitsC_eq_of_getD {l : List ℕ} (hl : l.length = L)
    (h : ∀ ℓ : Fin L, l.getD ℓ 0 = cubeIdx (π ℓ)) : digitsC π = l :=
  digitsStr_eq_of_getD cubeEquiv π hl h




end

theorem digitsC_injective (L : ℕ) : Function.Injective (digitsC : Cube L → List ℕ) :=
  digitsStr_injective _


/-- Every list of L digits below 10 is the list of digits of a leaf. -/
theorem exists_digitsT {L : ℕ} (l : List ℕ) (hl : l.length = L) (hd : ∀ d ∈ l, d < 10) :
    ∃ τ : Leaf L, digitsT τ = l := exists_digitsStr _ l hl hd

/-! ## The levels of a symbol are the positions of its digit -/



private theorem cubeIdx_star : (cubeIdx .star : ℕ) = 10 := rfl

theorem cubeIdx_term (lam : Term) : (cubeIdx (.term lam) : ℕ) = termIdx lam := rfl



/-- P₀ is the only term with the digit 9. -/
theorem termIdx_eq_nine (lam : Term) : (termIdx lam : ℕ) = 9 ↔ lam = .P0 := by
  cases lam with
  | P i j =>
    simp only [termIdx, reduceCtorEq, iff_false]
    omega
  | P0 => simp [termIdx]

section

variable {L : ℕ} (π : Cube L) (τ : Leaf L) (η : OutStr L)











/-- The number of symbols P₀ is the number of digits 9. -/
theorem card_P0Levels : (P0Levels τ).card = (digitsT τ).count 9 := by
  rw [digitsT, digitsStr, List.count_ofFn]
  exact congrArg Finset.card (Finset.filter_congr fun ℓ _ => (termIdx_eq_nine (τ ℓ)).symm)

end

/-! ## The lowest symbols P₀ turned into stars -/





theorem length_starFirst (e : ℕ) (l : List ℕ) : (starFirst e l).length = l.length := by
  fun_induction starFirst e l <;> simp_all

/-- The digits of `starFirst e l`: a digit 9 with fewer than e digits 9 before it becomes 10. -/
theorem getD_starFirst (e : ℕ) (l : List ℕ) (i : ℕ) :
    (starFirst e l).getD i 0
      = if l.getD i 0 = 9 ∧ (l.take i).count 9 < e then 10 else l.getD i 0 := by
  fun_induction starFirst e l generalizing i <;> cases i <;> simp_all

/-- Replacing the e lowest symbols P₀ of a leaf by stars is `starFirst e` on its digits. -/
theorem digitsC_starLowest {L : ℕ} (e : ℕ) (τ : Leaf L) :
    digitsC (starLowest e τ) = starFirst e (digitsT τ) := by
  refine digitsC_eq_of_getD _ (by rw [length_starFirst, length_digitsT]) fun ℓ => ?_
  have hcount : ((digitsT τ).take ℓ).count 9 = ((P0Levels τ).filter fun ℓ' => ℓ' < ℓ).card := by
    rw [digitsT, digitsStr, List.count_take_ofFn]
    refine congrArg Finset.card (Finset.ext fun ℓ' => ?_)
    rw [Finset.mem_filter_univ, Finset.mem_filter, P0Levels, Finset.mem_filter_univ, Fin.lt_def,
      and_comm]
    exact and_congr_left' (termIdx_eq_nine (τ ℓ'))
  have hmem : ℓ ∈ lowest e (P0Levels τ) ↔
      (digitsT τ).getD ℓ 0 = 9 ∧ ((digitsT τ).take ℓ).count 9 < e := by
    rw [hcount, getD_digitsT, termIdx_eq_nine, lowest, Finset.mem_filter, P0Levels,
      Finset.mem_filter_univ]
  rw [getD_starFirst, starLowest, Cube.starAt]
  by_cases hc : ℓ ∈ lowest e (P0Levels τ)
  · rw [if_pos hc, if_pos (hmem.mp hc), cubeIdx_star]
  · rw [if_neg hc, if_neg fun h => hc (hmem.mpr h), getD_digitsT, cubeIdx_term]

/-! ## Stars turned into P₀, and a symbol replaced by a term -/



/-- A list without the digit 10 is not changed. -/
theorem starsToNines_of_notMem {s : List ℕ} (h : 10 ∉ s) : starsToNines s = s := by
  rw [starsToNines]
  conv_rhs => rw [← List.map_id s]
  exact List.map_congr_left fun d hd => if_neg fun h' : d = 10 => h (h' ▸ hd)

/-- Turning the stars back into nines undoes `starFirst`. -/
theorem starsToNines_starFirst (e : ℕ) {l : List ℕ} (h : 10 ∉ l) :
    starsToNines (starFirst e l) = l := by
  fun_induction starFirst e l with
  | case1 l => exact starsToNines_of_notMem h
  | case2 => rfl
  | case3 e l ih => simp_all [starsToNines]
  | case4 e d l hd ih =>
    rw [starsToNines, List.map_cons, if_neg fun h10 : d = 10 => h (h10 ▸ List.mem_cons_self)]
    exact congrArg (d :: ·) (ih fun h' => h (List.mem_cons_of_mem _ h'))





/-! ## The highest star -/











/-! ## The dynamic program of Lemma 29 on digits -/

















end ThreeSumApsp.Spec

end

end


-- Original source module: ThreeSumApsp.Spec.Sec4.Theorem30.StarBoxes
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The boxes with e stars, as a list (proof of Lemma 29)

"A box in which f of the symbols are P₀ or stars is obtained from a leaf of order m - f (namely the
leaf we get by replacing its stars with P₀) by turning the e lowest symbols P₀ of that leaf into
stars, for some e ≤ f."  So the boxes with exactly e stars are the leaves with between e and m - t
symbols P₀, with the first e digits 9 turned into 10: this is `starBoxes`.

The list contains exactly the boxes with e stars (`mem_starBoxes`, `exists_of_mem_starBoxes`), each
of them once (`starBoxes_nodup`), so it has as many members as there are such boxes
(`length_starBoxes`), and all lists together have as many members as there are boxes
(`sum_length_starBoxes`).

The lists are the order of work of Lemma 29: "We compute the values of the boxes in increasing order
of their number of stars", "Generating the boxes with e stars and inserting them into the trie".
All of them go into the trie of the tile.  The number of stars can be read off a box
(`starCount_of_mem_starBoxes`), so boxes from different lists are different strings, and a string
is a box exactly if it is in the list for its number of stars (`isBoxDigits_digitsC`).  There are
boxes with e stars only for e ≤ m - t (`le_of_mem_starBoxes`).  Replacing the highest star of a box
with e + 1 stars by a term gives a box with e stars (`exists_lastStar_of_mem_starBoxes`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec







/-- A member of the list comes from a leaf with between e and m - t symbols P₀. -/
private theorem exists_leaf_of_mem_starBoxes {L m t e : ℕ} {l : List ℕ}
    (h : l ∈ starBoxes L m t e) :
    ∃ τ : Leaf L, e ≤ (P0Levels τ).card ∧ (P0Levels τ).card ≤ m - t ∧
      digitsC (starLowest e τ) = l := by
  obtain ⟨l', hl', rfl⟩ := List.mem_map.1 h
  obtain ⟨hlen, hdig, hlo, hhi⟩ := (mem_nineStrs l').1 hl'
  obtain ⟨τ, rfl⟩ := exists_digitsT (L := L) l' hlen hdig
  exact ⟨τ, by rwa [card_P0Levels], by rwa [card_P0Levels], digitsC_starLowest e τ⟩

/-- The list contains exactly the boxes with e stars. -/
theorem mem_starBoxes {L : ℕ} (m t e : ℕ) (π : Cube L) :
    digitsC π ∈ starBoxes L m t e ↔ π ∈ boxesWithStars L m t e := by
  rw [mem_boxesWithStars]
  constructor
  · intro h
    obtain ⟨τ, hlo, hhi, hτ⟩ := exists_leaf_of_mem_starBoxes h
    obtain rfl : π = starLowest e τ := digitsC_injective L hτ.symm
    refine ⟨isBox_starLowest m t e τ hhi, ?_⟩
    rw [starLevels_starLowest, card_lowest]
    omega
  · rintro ⟨hbox, he⟩
    have hπ := eq_starLowest_starsToP0 π hbox.2
    have hcard := card_P0Levels_starsToP0 π
    rw [he] at hπ
    refine List.mem_map.2 ⟨digitsT (Cube.starsToP0 π),
      (mem_nineStrs _).2 ⟨length_digitsT _, digitsT_lt _, ?_, ?_⟩, ?_⟩
    · rw [← card_P0Levels]
      omega
    · rw [← card_P0Levels, hcard]
      exact hbox.1
    · rw [← digitsC_starLowest, ← hπ]

/-- Every member of the list is a cube. -/
theorem exists_of_mem_starBoxes {L m t e : ℕ} (l : List ℕ) (h : l ∈ starBoxes L m t e) :
    ∃ π : Cube L, digitsC π = l := by
  obtain ⟨τ, -, -, hτ⟩ := exists_leaf_of_mem_starBoxes h
  exact ⟨_, hτ⟩















/-- No box occurs twice in the list: turning the stars back into nines gives the leaf. -/
theorem starBoxes_nodup (L m t e : ℕ) : (starBoxes L m t e).Nodup := by
  refine (nineStrs_nodup _ _ _).map_on fun x hx y hy h => ?_
  rw [← starsToNines_starFirst e (ten_notMem_of_mem_nineStrs hx), h,
    starsToNines_starFirst e (ten_notMem_of_mem_nineStrs hy)]

/-- The list has as many members as there are boxes with e stars. -/
theorem length_starBoxes (L m t e : ℕ) :
    (starBoxes L m t e).length = (boxesWithStars L m t e).card := by
  classical
  have himage : (boxesWithStars L m t e).image digitsC = (starBoxes L m t e).toFinset := by
    ext l
    rw [Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨π, hπ, rfl⟩
      exact (mem_starBoxes m t e π).2 hπ
    · intro hl
      obtain ⟨π, rfl⟩ := exists_of_mem_starBoxes l hl
      exact ⟨π, (mem_starBoxes m t e π).1 hl, rfl⟩
  rw [← List.toFinset_card_of_nodup (starBoxes_nodup L m t e), ← himage,
    Finset.card_image_of_injective _ (digitsC_injective L)]

/-- All lists together have as many members as there are boxes (Lemma 29). -/
theorem sum_length_starBoxes (L m t : ℕ) :
    ((List.range (m - t + 1)).map fun e => (starBoxes L m t e).length).sum
      = (boxes L m t).card := by
  have hfibres : (boxes L m t).card = ∑ e ∈ Finset.range (m - t + 1),
      ((boxes L m t).filter fun π => (Cube.starLevels π).card = e).card := by
    refine Finset.card_eq_sum_card_fiberwise fun π hπ => ?_
    have := (mem_boxes.1 (Finset.mem_coe.1 hπ)).1
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  rw [List.sum_map_range, hfibres]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [length_starBoxes]
  refine congrArg Finset.card (Finset.ext fun π => ?_)
  rw [mem_boxesWithStars, Finset.mem_filter, mem_boxes]

end ThreeSumApsp.Spec

end

end


-- Original source module: ThreeSumApsp.Programs.Sec4.Theorem30.Time
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Theorem 30 in the light language: the tiles and a query against the expressions (8) and L ∑ α_d

Pure arithmetic. The routines of Section 4 have explicit time functions. This file and the next one
show that, under the hypotheses of Theorem 30 (`Hyp30`), time and space of the preprocessing are at
most a constant times the expression (8), and the time of a query is at most a constant times
L ∑_{d ≤ t} α_d.

`Within8 f` says that f is at most a constant times (8). Such bounds can be added, multiplied by a
number and passed to smaller functions. Four quantities are within (8) by the counts in the proof of
Theorem 30: the number 1, the number 10^L of leaves, the work 10^L + L 7^L for each band, and L for
each box of each tile (`within8_one` to `within8_boxes`); the next file adds a fifth, N (L + 1)
(`within8_N_mul`). Every other function is bounded by a multiple of a sum of these: here the time
for all tiles (`within8_tAllTiles`) and the space of their tries (`within8_trieSpace`). For a query
see `exists_tQueryCore_le`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec Finset

/-! ## The hypotheses of Theorem 30, and what lies within (8) -/



theorem Hyp30.m_le {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) : p.m ≤ p.L := by
  have := h.L_ge
  omega

theorem Hyp30.L_pos {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) : 1 ≤ p.L := by
  have := h.L_ge
  have := h.m_pos
  omega

/-- `10^L` is within (8): it is at most the last term. -/
theorem ten_pow_le_cost8 {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) :
    (10 : ℝ) ^ p.L ≤ cost8 p.L p.m t p.N := by
  have hfirst := cost8_first_term_nonneg t p.N h.L_ge
  have hlast := Theorem30.subsets_absorbed h.L_ge h.N_ge
  rw [cost8_eq]
  linarith

/-- The expression (8) is at least 1. -/
theorem one_le_cost8 (L m t N : ℕ) (hL : 10 * m ≤ L)
    (hN : sqrtKN0 L m ≤ (N : ℝ)) : 1 ≤ cost8 L m t N := by
  have hfirst := cost8_first_term_nonneg t N hL
  have hlast := Theorem30.subsets_absorbed hL hN
  have hone : (1 : ℝ) ≤ (10 : ℝ) ^ L := one_le_pow₀ (by norm_num)
  rw [cost8_eq]
  linarith



namespace Within8

variable {f g : Sec2.Par → ℕ → ℕ}

/-- A smaller function. -/
theorem of_le (hg : Within8 g) (h : ∀ p t, Hyp30 p t → f p t ≤ g p t) : Within8 f :=
  let ⟨C, hC, hg⟩ := hg
  ⟨C, hC, fun p t hp => le_trans (by exact_mod_cast h p t hp) (hg p t hp)⟩

theorem add (hf : Within8 f) (hg : Within8 g) : Within8 fun p t => f p t + g p t := by
  obtain ⟨A, hA, hf⟩ := hf
  obtain ⟨B, hB, hg⟩ := hg
  refine ⟨A + B, add_nonneg hA hB, fun p t hp => ?_⟩
  rw [Nat.cast_add, add_mul]
  exact add_le_add (hf p t hp) (hg p t hp)

theorem const_mul (c : ℕ) (hf : Within8 f) : Within8 fun p t => c * f p t := by
  obtain ⟨A, hA, hf⟩ := hf
  refine ⟨c * A, by positivity, fun p t hp => ?_⟩
  rw [Nat.cast_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf p t hp) (Nat.cast_nonneg c)

end Within8

theorem within8_one : Within8 fun _ _ => 1 :=
  ⟨1, zero_le_one, fun p t h => by simpa using one_le_cost8 p.L p.m t p.N h.L_ge h.N_ge⟩

theorem within8_ten_pow : Within8 fun p _ => 10 ^ p.L :=
  ⟨1, zero_le_one, fun p t h => by simpa using ten_pow_le_cost8 h⟩

/-- The work for the bands: `10^L + L 7^L` for each band. -/
theorem within8_bands : Within8 fun p _ => p.nB * (10 ^ p.L + p.L * 7 ^ p.L) := by
  refine ⟨13 / 2, by norm_num, fun p t h => ?_⟩
  have hsum := Theorem30.cost8_assembly h.m_pos h.L_ge h.t_le h.N_ge
  have hboxes :
      0 ≤ (p.L : ℝ) * ((numBands p.L p.m p.N : ℝ) ^ 2 * ((boxes p.L p.m t).card : ℝ)) := by
    positivity
  have htable : 0 ≤ (K p.L p.m : ℝ) * (p.L : ℝ) := by positivity
  push_cast
  change (numBands p.L p.m p.N : ℝ) * _ ≤ _
  linarith

/-- The work for the boxes: `L` for each box of each tile. -/
theorem within8_boxes : Within8 fun p t => p.L * (p.nB ^ 2 * (boxes p.L p.m t).card) := by
  refine ⟨13, by norm_num, fun p t h => ?_⟩
  have hsum := Theorem30.cost8_assembly h.m_pos h.L_ge h.t_le h.N_ge
  have hbands :
      0 ≤ 2 * (numBands p.L p.m p.N : ℝ) * ((10 : ℝ) ^ p.L + (p.L : ℝ) * (7 : ℝ) ^ p.L) := by
    positivity
  have htable : 0 ≤ (K p.L p.m : ℝ) * (p.L : ℝ) := by positivity
  push_cast
  change (p.L : ℝ) * ((numBands p.L p.m p.N : ℝ) ^ 2 * _) ≤ _
  linarith

/-! ## The tiles -/

/-- For every e ≤ m - t with e ≤ L there is a box with e stars. -/
theorem one_le_length_starBoxes {L m t e : ℕ} (he : e ≤ m - t) (hL : e ≤ L) :
    1 ≤ (starBoxes L m t e).length := by
  have hhead := head?_nineStrs (n := L) (lo := e) (hi := m - t) hL he
  rw [starBoxes, List.length_map]
  cases hl : nineStrs L e (m - t) with
  | nil => rw [hl] at hhead; simp at hhead
  | cons a l => simp

/-- There are at least m - t + 1 boxes: one for each number of stars. -/
theorem succ_le_card_boxes {L m t : ℕ} (hL : m ≤ L) : m - t + 1 ≤ (boxes L m t).card := by
  have hsum := List.length_le_sum_of_one_le
    ((List.range (m - t + 1)).map fun e => (starBoxes L m t e).length) fun n hn => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hn
      have := List.mem_range.1 he
      exact one_le_length_starBoxes (by omega) (by omega)
  rwa [sum_length_starBoxes, List.length_map, List.length_range] at hsum

/-- The time for a tile, in closed form. -/
theorem tTile_eq (L m t : ℕ) : tTile L m t
    = tNewRoot + (m - t + 1) * (tNineFirst L + 120) + (boxes L m t).card * tFillStep L + 60 := by
  have hrounds : ∀ k, ((List.range k).map fun e => tFillList L (starBoxes L m t e).length + 60).sum
      = k * (tNineFirst L + 120)
        + ((List.range k).map fun e => (starBoxes L m t e).length).sum * tFillStep L := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, tFillList]
      ring
  rw [tTile, hrounds, sum_length_starBoxes]
  ring

/-- The time for a tile, and what the loop over the tiles adds to it, is O(L) for each box (Lemma
29). The enumeration of the boxes with e stars is started once for each e ≤ m - t, in O(L) steps
each time; these m - t + 1 starts are paid for by the boxes, of which there are at least m - t + 1
(succ_le_card_boxes). -/
private theorem exists_tTile_le : ∃ c : ℕ, ∀ L m t : ℕ, 1 ≤ L → m ≤ L →
    tTile L m t + 120 ≤ c * (L * (boxes L m t).card) := by
  refine ⟨2000, fun L m t hL1 hmL => ?_⟩
  have hcard := succ_le_card_boxes (t := t) hmL
  have hstarts : (m - t + 1) * (tNineFirst L + 120) ≤ (boxes L m t).card * (tNineFirst L + 120) :=
    Nat.mul_le_mul_right _ hcard
  rw [tTile_eq]
  simp only [tFillStep, tFillRound, tStarFirst, tHorner, tSumTen, tLookup, tInsert, tNineNext,
    tNewRoot, tNineFirst] at hstarts ⊢
  generalize (boxes L m t).card = b at *
  have hb : b ≤ L * b := Nat.le_mul_of_pos_left _ hL1
  rw [show b * (30 * L + 30 + 120) = 30 * (L * b) + 150 * b by ring] at hstarts
  rw [show b * (50 * L + 30 + (20 * L + 10) + (10 * (20 * L + 12 + 40) + 30) + (220 * L + 20)
    + (90 * L + 60) + 120) = 580 * (L * b) + 790 * b by ring]
  omega

/-- **The tries of all tiles** are built within (8). -/
theorem within8_tAllTiles : Within8 fun p t => tAllTiles p.L p.m t p.nB := by
  obtain ⟨c, hc⟩ := exists_tTile_le
  refine ((within8_boxes.const_mul c).add (within8_one.const_mul 30)).of_le fun p t h => ?_
  have htile := hc p.L p.m t h.L_pos h.m_le
  have hn : p.nB ≤ p.nB ^ 2 := Nat.le_self_pow (by norm_num) _
  calc tAllTiles p.L p.m t p.nB
      = p.nB ^ 2 * (tTile p.L p.m t + 80) + p.nB * 40 + 30 := by simp only [tAllTiles]; ring
    _ ≤ p.nB ^ 2 * (tTile p.L p.m t + 80) + p.nB ^ 2 * 40 + 30 := by gcongr
    _ = p.nB ^ 2 * (tTile p.L p.m t + 120) + 30 := by ring
    _ ≤ p.nB ^ 2 * (c * (p.L * (boxes p.L p.m t).card)) + 30 := by gcongr
    _ = c * (p.L * (p.nB ^ 2 * (boxes p.L p.m t).card)) + 30 * 1 := by ring



/-! ## A query -/

/-- The query cost of Theorem 30 is at least L. -/
theorem cast_L_le_costQuery (L m t : ℕ) : (L : ℝ) ≤ costQuery L m t := by
  have hsum : (1 : ℝ) ≤ ∑ d ∈ range (t + 1), (alpha m d : ℝ) := by
    rw [show (1 : ℝ) = (alpha m 0 : ℝ) by simp [alpha]]
    exact single_le_sum (f := fun d => (alpha m d : ℝ)) (fun _ _ => by positivity) (by simp)
  exact le_mul_of_one_le_right (Nat.cast_nonneg L) hsum



/-- **A query**, once the digits of its output string are known, takes O(L) steps for each number
that it reads. -/
theorem exists_tQueryCore_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ L m t : ℕ, 1 ≤ L → m ≤ L → t ≤ m →
    (tQueryCore L m t : ℝ) ≤ C * costQuery L m t := by
  refine ⟨900, by norm_num, fun L m t hL1 hmL ht => ?_⟩
  have hnat : tQueryCore L m t ≤ 900 * (L * ∑ d ∈ range (t + 1), alpha m d) := by
    have hpos : 1 ≤ alpha m t := Nat.mul_pos (Nat.choose_pos ht) (by positivity)
    rw [tQueryCore, length_lowList ht [], length_boxesOf ht [], sum_range_succ]
    simp only [tScatter, tHorner, tLookup, tNineNext, tNineFirst]
    generalize ∑ d ∈ range t, alpha m d = low
    generalize alpha m t = a at *
    have hlow : low * (60 * L + 30 + (20 * L + 10) + (90 * m + 60) + 90) ≤ low * (360 * L) :=
      Nat.mul_le_mul_left _ (by omega)
    have hboxes : a * (60 * L + 30 + (20 * L + 12) + (90 * m + 60) + 90) ≤ a * (362 * L) :=
      Nat.mul_le_mul_left _ (by omega)
    have hL : L ≤ a * L := Nat.le_mul_of_pos_left _ hpos
    rw [show 900 * (L * (low + a))
      = low * (360 * L) + a * (362 * L) + 540 * (low * L) + 538 * (a * L) by ring]
    omega
  unfold costQuery
  exact_mod_cast hnat

end Light.Sec4

end

end


-- Original source module: ThreeSumApsp.Programs.Sec4.Theorem30.TimeOfBlock
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Theorem 30 in the light language: the two routines against the expressions (8) and L ∑ α_d

Pure arithmetic, continued. Every summand of the time of the shared stage and of the length of the
shared block is at most a constant times `10^L`, or `N (L + 1)`, or the work for the bands
(`sharedShape_le`, `sharedEnd_sub_le`), and these three are within (8). With the tiles of the
previous file this gives the three bounds that leave these two files: the preprocessing takes
`O((8))` steps (`exists_tPreCore_le`), the block has `O((8))` cells (`exists_top_sub_le`), and a
query takes `O(L ∑_{d ≤ t} α_d)` steps (`exists_tQueryAt_le`).  The offline form uses them
elsewhere: its expression (9) is (8) plus |W| times the cost of a query (`Theorem30.cost9_eq`, with
the mathematics of Theorem 30), and `exists_tWantedCore_le`, beside the offline statement, puts the
two bounds together.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec Finset

/-! ## The shared stage, in natural numbers -/

/-- `(L + 1)² ≤ 10^L`. -/
theorem succ_sq_le_ten_pow (L : ℕ) : (L + 1) ^ 2 ≤ 10 ^ L := by
  have hfour : (L + 1) ^ 2 ≤ 4 ^ L := by
    induction L with
    | zero => simp
    | succ L ih =>
      calc (L + 1 + 1) ^ 2 ≤ 4 * (L + 1) ^ 2 := by
            rw [show (L + 1 + 1) ^ 2 = L * L + 4 * L + 4 by ring,
              show 4 * (L + 1) ^ 2 = 4 * (L * L) + 8 * L + 4 by ring]
            omega
        _ ≤ 4 * 4 ^ L := Nat.mul_le_mul_left _ ih
        _ = 4 ^ (L + 1) := by ring
  exact hfour.trans (Nat.pow_le_pow_left (by norm_num) L)



private theorem sizeFacts (p : Sec2.Par) (hL1 : 1 ≤ p.L) (hmL : p.m ≤ p.L) :
    SizeFacts p.L p.m p.K p.KK p.N0 p.D p.S7 p.T :=
  ⟨succ_sq_le_ten_pow p.L, Theorem30.subsets p.L p.m, Theorem30.K_mul_N0_mul_D_le p.L p.m,
    Theorem30.form_array p.L, Nat.pow_le_pow_left (by norm_num) p.L, Nat.sqrt_le _,
    Nat.choose_pos hmL, Nat.one_le_pow _ _ (by norm_num), Nat.one_le_pow _ _ (by norm_num), hL1,
    hmL⟩

/-- The time of the shared stage: a part of order `10^L`, a part of order `N L`, and a part for each
band. -/
theorem sharedShape_le (p : Sec2.Par) (hL1 : 1 ≤ p.L) (hmL : p.m ≤ p.L) : Sec2.sharedShape p
    ≤ 11 * 10 ^ p.L + (p.N + 1) * (p.L + 1) + p.nB * (3 * (10 ^ p.L + p.L * 7 ^ p.L)) := by
  obtain ⟨sq, KL, KND, LS, ST, KKle, K1, N1, D1, L1, mL⟩ := sizeFacts p hL1 hmL
  have hsqrt : Nat.sqrt p.K ≤ p.K := Nat.sqrt_le_self _
  have hLo : p.Lo ≤ p.L := Nat.sub_le _ _
  unfold Sec2.sharedShape Sec2.bandArrayShape
  change _ ≤ 11 * p.T + (p.N + 1) * (p.L + 1) + p.nB * (3 * (p.T + p.L * p.S7))
  generalize p.T = T at *
  generalize p.S7 = S7 at *
  generalize p.K = K at *
  generalize p.KK = KK at *
  generalize p.N0 = N0 at *
  generalize p.D = D at *
  generalize p.nB = nB at *
  generalize p.Lo = Lo at *
  generalize p.N = N at *
  generalize p.L = L at *
  generalize p.m = m at *
  have hLT : L + 1 ≤ T := (Nat.le_self_pow (by norm_num) _).trans sq
  have hKT : K ≤ T := le_trans (Nat.le_mul_of_pos_right _ L1) KL
  have hDS : D ≤ S7 := le_trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos K1 N1)) KND
  have hentries : KK * N0 * D ≤ S7 :=
    le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ KKle)) KND
  have hSL : S7 ≤ L * S7 := Nat.le_mul_of_pos_left _ L1
  -- the summands, one after the other
  have htable : (KK + 1) * (L + 1) ≤ K * L + K + L + 1 :=
    (Nat.mul_le_mul_right _ (by omega) : _ ≤ (K + 1) * (L + 1)).trans (le_of_eq (by ring))
  have hdig4 : (D + 1) * (m + 1) ≤ L * S7 + S7 + L + 1 :=
    (Nat.mul_le_mul (by omega) (by omega) : _ ≤ (S7 + 1) * (L + 1)).trans (le_of_eq (by ring))
  have harray : (KK * N0 * D + 1) * (L + 1) ≤ L * S7 + S7 + L + 1 :=
    (Nat.mul_le_mul_right _ (by omega) : _ ≤ (S7 + 1) * (L + 1)).trans (le_of_eq (by ring))
  have hdig3 : (N + 1) * (Lo + 1) ≤ (N + 1) * (L + 1) := Nat.mul_le_mul_left _ (by omega)
  have hbands : nB * (T + (S7 + (KK * N0 * D + 1) * (L + 1))) ≤ nB * (3 * (T + L * S7)) :=
    Nat.mul_le_mul_left _ (by omega)
  omega



/-! ## Within (8) -/

/-- `N (L + 1)` is within three times (8), because `√K N₀ ≤ 7^L` and `(L + 1) 7^L ≤ 3 · 10^L`. -/
theorem N_mul_le_cost8 {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) :
    (p.N : ℝ) * ((p.L : ℝ) + 1) ≤ 3 * cost8 p.L p.m t p.N := by
  have hpos := sqrtKN0_pos h.m_le
  have hfirst := cost8_first_term_nonneg t p.N h.L_ge
  have hKN : (K p.L p.m : ℝ) * (N0 p.L p.m : ℝ) ≤ (7 : ℝ) ^ p.L := by
    exact_mod_cast le_trans (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by norm_num)))
      (Theorem30.K_mul_N0_mul_D_le p.L p.m)
  have htile : sqrtKN0 p.L p.m ≤ (7 : ℝ) ^ p.L := (sqrtKN0_le h.m_le).trans hKN
  have hseven : ((p.L : ℝ) + 1) * (7 : ℝ) ^ p.L ≤ 3 * (10 : ℝ) ^ p.L := by
    have harray := Theorem30.form_array p.L
    have hpow : 7 ^ p.L ≤ 10 ^ p.L := Nat.pow_le_pow_left (by norm_num) p.L
    exact_mod_cast (by rw [Nat.add_one_mul]; omega : (p.L + 1) * 7 ^ p.L ≤ 3 * 10 ^ p.L)
  -- N (L + 1) √K N₀ ≤ N (L + 1) 7^L ≤ 3 N 10^L, which is 3 √K N₀ times the last term of (8)
  have hlast : (p.N : ℝ) * ((p.L : ℝ) + 1)
      ≤ 3 * ((p.N : ℝ) * (10 : ℝ) ^ p.L / sqrtKN0 p.L p.m) := by
    rw [← mul_div_assoc, le_div_iff₀ hpos]
    calc (p.N : ℝ) * ((p.L : ℝ) + 1) * sqrtKN0 p.L p.m
        ≤ (p.N : ℝ) * ((p.L : ℝ) + 1) * (7 : ℝ) ^ p.L :=
          mul_le_mul_of_nonneg_left htile (by positivity)
      _ = (p.N : ℝ) * (((p.L : ℝ) + 1) * (7 : ℝ) ^ p.L) := by ring
      _ ≤ (p.N : ℝ) * (3 * (10 : ℝ) ^ p.L) := mul_le_mul_of_nonneg_left hseven (Nat.cast_nonneg _)
      _ = 3 * ((p.N : ℝ) * (10 : ℝ) ^ p.L) := by ring
  rw [cost8_eq]
  linarith

/-- `N 4^m` is within (8): it is at most the last term, because `√K N₀ 4^m ≤ K N₀ 4^m ≤ 7^L ≤ 10^L`.
-/
theorem N_mul_pow_le_cost8 {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) :
    (p.N : ℝ) * (4 : ℝ) ^ p.m ≤ cost8 p.L p.m t p.N := by
  have hfirst := cost8_first_term_nonneg t p.N h.L_ge
  have hKND : K p.L p.m * N0 p.L p.m * 4 ^ p.m ≤ 10 ^ p.L :=
    (Theorem30.K_mul_N0_mul_D_le p.L p.m).trans (Nat.pow_le_pow_left (by norm_num) _)
  have hlast : (p.N : ℝ) * (4 : ℝ) ^ p.m ≤ (p.N : ℝ) * (10 : ℝ) ^ p.L / sqrtKN0 p.L p.m := by
    rw [le_div_iff₀ (sqrtKN0_pos h.m_le), mul_assoc]
    gcongr
    calc (4 : ℝ) ^ p.m * sqrtKN0 p.L p.m
        ≤ (4 : ℝ) ^ p.m * ((K p.L p.m : ℝ) * (N0 p.L p.m : ℝ)) := by
          gcongr
          exact sqrtKN0_le h.m_le
      _ = ((K p.L p.m * N0 p.L p.m * 4 ^ p.m : ℕ) : ℝ) := by
          push_cast
          ring
      _ ≤ (10 : ℝ) ^ p.L := by exact_mod_cast hKND
  rw [cost8_eq]
  linarith

theorem within8_N_mul : Within8 fun p _ => p.N * (p.L + 1) :=
  ⟨3, by norm_num, fun p t h => by
    push_cast
    exact N_mul_le_cost8 h⟩

/-- The three quantities that bound the shared stage, together. -/
private theorem within8_shared :
    Within8 fun p _ => 10 ^ p.L + p.N * (p.L + 1) + p.nB * (10 ^ p.L + p.L * 7 ^ p.L) :=
  (within8_ten_pow.add within8_N_mul).add within8_bands

/-- **The shared stage** runs within (8). -/
theorem within8_sharedShape : Within8 fun p _ => Sec2.sharedShape p := by
  refine (within8_shared.const_mul 12).of_le fun p t h => ?_
  have hshape := sharedShape_le p h.L_pos h.m_le
  have hLT : p.L + 1 ≤ 10 ^ p.L :=
    (Nat.le_self_pow (by norm_num) _).trans (succ_sq_le_ten_pow p.L)
  rw [Nat.add_one_mul p.N, ← Nat.mul_assoc, Nat.mul_comm p.nB 3, Nat.mul_assoc] at hshape
  omega

/-- **The preprocessing** takes `O((8))` steps.  c is the constant of the shared stage. -/
theorem exists_tPreCore_le (c : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Sec2.Par) (t : ℕ), Hyp30 p t →
    (tPreCore c p t : ℝ) ≤ C * cost8 p.L p.m t p.N :=
  (((within8_sharedShape.const_mul c).add within8_tAllTiles).add (within8_one.const_mul 300)).of_le
    fun _ _ _ => le_of_eq (by simp [tPreCore])





/-- **A query** takes `O(L ∑_{d ≤ t} α_d)` steps. -/
theorem exists_tQueryAt_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Sec2.Par) (t : ℕ), Hyp30 p t →
    (tQueryAt p.L p.m t : ℝ) ≤ C * costQuery p.L p.m t := by
  obtain ⟨C, hC, hcore⟩ := exists_tQueryCore_le
  refine ⟨C + 510, by positivity, fun p t h => ?_⟩
  have hcore := hcore p.L p.m t h.L_pos h.m_le h.t_le
  have hL := cast_L_le_costQuery p.L p.m t
  have hL1 : (1 : ℝ) ≤ p.L := by exact_mod_cast h.L_pos
  -- tQueryAt = 70 L + 440 + tQueryCore
  unfold tQueryAt tOutDigits
  push_cast
  linarith

end Light.Sec4

end

end


-- Original source module: ThreeSumApsp.Programs.Sec4.ChoosingParameters.Costs
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Section 4.4: the costs of the programs with rational parameters

Bounds for the time and the space of the preprocessing and for the time of a query. `CostsWithin`
says of two bounds tp and tq that they dominate the two costs of Theorem 30. A quantity that is
bounded for m < m₀ and within a constant times a cost for m ≥ m₀ is then within a constant times the
bound (`exists_le_of_small_of_large`). The overheads are absorbed by the cost expression (8) of
Theorem 30: padding, copying and filling cost O(N 4^m), and N 4^m ≤ N 10^L/(√K N₀), because K N₀ 4^m
≤ 7^L (`N_mul_pow_le_cost8`); computing L and t costs O(L). For m < m₀ everything is bounded by a
constant. This gives the results that the end theorems use: `exists_tPre31_le`,
`exists_tQuery31_le`, `exists_tOffline32_le`, `exists_structEnd_sub_le`, `exists_lim31_depth_le`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec ThreeSumApsp.WordRam

section
variable (G : RatParams)



variable {G} in
/-- For m ≥ m₀ the hypotheses of Theorem 30 hold. -/
theorem CostsWithin.hyp {C : ℝ} {N D₀ : ℕ} {tp tq : ℝ} (h : CostsWithin G C N D₀ tp tq)
    (hm : G.m₀ ≤ logFour D₀) : G.Hyp N D₀ :=
  (h.above hm).1

variable {G} in
/-- For m ≥ m₀ the cost (8) is at most C tp. -/
theorem CostsWithin.pre_le {C : ℝ} {N D₀ : ℕ} {tp tq : ℝ} (h : CostsWithin G C N D₀ tp tq)
    (hm : G.m₀ ≤ logFour D₀) : G.preCost N D₀ ≤ C * tp :=
  (h.above hm).2.1

variable {G} in
/-- For m ≥ m₀ the cost of a query is at most C tq. -/
theorem CostsWithin.query_le {C : ℝ} {N D₀ : ℕ} {tp tq : ℝ} (h : CostsWithin G C N D₀ tp tq)
    (hm : G.m₀ ≤ logFour D₀) : G.queryCost D₀ ≤ C * tq :=
  (h.above hm).2.2

/-- A quantity that is bounded below the threshold, and at most a constant times a cost from the
threshold on, is at most a constant times every bound t ≥ 1 that dominates the cost. -/
theorem exists_le_of_small_of_large {C : ℝ} (hC : 0 ≤ C) {S K : ℝ} (hS : 0 ≤ S) (hK : 0 ≤ K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (D₀ : ℕ) (cost t z : ℝ), 1 ≤ t → (G.m₀ ≤ logFour D₀ → cost ≤ C * t) →
      (logFour D₀ < G.m₀ → z ≤ S) → (G.m₀ ≤ logFour D₀ → z ≤ K * cost + S) → z ≤ A * t := by
  refine ⟨S + K * C, by positivity, fun D₀ cost t z ht hcost hsmall hlarge => ?_⟩
  have hsplit : (S + K * C) * t = S * t + K * (C * t) := by ring
  have hSt : S ≤ S * t := le_mul_of_one_le_right hS ht
  rw [hsplit]
  by_cases hm : logFour D₀ < G.m₀
  · linarith [hsmall hm, mul_nonneg hK (mul_nonneg hC (by linarith : (0 : ℝ) ≤ t))]
  · linarith [hlarge (by omega), mul_le_mul_of_nonneg_left (hcost (by omega)) hK]

/-! ### The preprocessing -/

/-- Setting up takes O(L + N 4^m) steps. -/
theorem exists_tPre31_le_setup : ∃ k : ℕ, ∀ c0 N D₀ : ℕ, G.m₀ ≤ logFour D₀ →
    tPre31 c0 G N D₀ ≤ k * (G.L (logFour D₀) + 1 + N * 4 ^ logFour D₀ + N)
      + tPreCore c0 (parOf G N D₀) (switchOf31 G D₀) := by
  refine ⟨20 + 20 * G.b + 20 * G.q + 352, fun c0 N D₀ hm => ?_⟩
  have ham := G.am_le (logFour D₀)
  have hpm := G.pm_le (logFour D₀)
  have hmL : logFour D₀ ≤ G.L (logFour D₀) := by have := G.ten_le_L (logFour D₀); omega
  have hDF : D₀ ≤ 4 ^ logFour D₀ := le_D_logFour D₀
  unfold tPre31
  rw [if_neg (not_lt.2 hm)]
  simp only [tLog4, tCeilMul, tPadX, tCopy, tFill, D]
  generalize tPreCore c0 (parOf G N D₀) (switchOf31 G D₀) = tp
  generalize G.L (logFour D₀) = L at *
  generalize logFour D₀ = m at *
  generalize 4 ^ m = F at *
  have hcopy : D₀ * N ≤ N * F := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hDF
  have hfill : (F - D₀) * N ≤ N * F := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hqL : G.q * m ≤ G.q * L := Nat.mul_le_mul_left _ hmL
  have hpad : N * (16 * F + 80) = 16 * (N * F) + 80 * N := by ring
  have hk : (20 + 20 * G.b + 20 * G.q + 352) * (L + 1 + N * F + N)
      = 20 * L + 20 * (G.b * L) + 20 * (G.q * L) + (20 + 20 * G.b + 20 * G.q) * (1 + N * F + N)
        + 352 * (L + 1 + N * F + N) := by ring
  have := Nat.zero_le ((20 + 20 * G.b + 20 * G.q) * (1 + N * F + N))
  omega

/-- From the threshold on the preprocessing takes O((8)) steps. -/
theorem exists_tPre31_le_cost8 (c0 : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ N D₀ : ℕ, 1 ≤ N → G.m₀ ≤ logFour D₀ →
    G.Hyp N D₀ → (tPre31 c0 G N D₀ : ℝ) ≤ K * G.preCost N D₀ := by
  obtain ⟨k, hk⟩ := exists_tPre31_le_setup G
  obtain ⟨Cp, hCp0, hCp⟩ := exists_tPreCore_le c0
  refine ⟨k * 7 + Cp, by positivity, fun N D₀ hN hm h => ?_⟩
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hL0 : (0 : ℝ) ≤ (G.L (logFour D₀) : ℝ) := by positivity
  have hcore : (tPreCore c0 (parOf G N D₀) (switchOf31 G D₀) : ℝ)
      ≤ Cp * G.preCost N D₀ := hCp (parOf G N D₀) (switchOf31 G D₀) h
  have hNF : (N : ℝ) * (4 : ℝ) ^ logFour D₀ ≤ G.preCost N D₀ := N_mul_pow_le_cost8 h
  have hNL : (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) ≤ 3 * G.preCost N D₀ := N_mul_le_cost8 h
  have hsetup : (tPre31 c0 G N D₀ : ℝ)
      ≤ k * ((G.L (logFour D₀) : ℝ) + 1 + N * (4 : ℝ) ^ logFour D₀ + N)
        + (tPreCore c0 (parOf G N D₀) (switchOf31 G D₀) : ℝ) := by exact_mod_cast hk c0 N D₀ hm
  -- L + 1 ≤ N (L + 1) and N ≤ N (L + 1), so that the sum is at most 7 times (8)
  have hL : (G.L (logFour D₀) : ℝ) + 1 ≤ (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) :=
    le_mul_of_one_le_left (by positivity) hN'
  have hNle : (N : ℝ) ≤ (N : ℝ) * ((G.L (logFour D₀) : ℝ) + 1) :=
    le_mul_of_one_le_right (by positivity) (by linarith)
  have hsum : (k : ℝ) * ((G.L (logFour D₀) : ℝ) + 1 + N * (4 : ℝ) ^ logFour D₀ + N)
      ≤ k * (7 * G.preCost N D₀) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- **The time of the preprocessing** is at most a constant times every bound tp ≥ 1 that, from the
threshold on, dominates the cost (8) of Theorem 30. -/
theorem exists_tPre31_le {C : ℝ} (hC : 0 ≤ C) (c0 : ℕ) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ {N D₀ : ℕ} {tp tq : ℝ}, CostsWithin G C N D₀ tp tq → (tPre31 c0 G N D₀ : ℝ) ≤ A * tp := by
  obtain ⟨K, hK0, hK⟩ := exists_tPre31_le_cost8 G c0
  obtain ⟨A, hA0, hA⟩ := exists_le_of_small_of_large G hC
    (S := ((20 * G.m₀ + 50 : ℕ) : ℝ)) (by positivity) hK0
  refine ⟨A, hA0, fun {N D₀ tp tq} h =>
    hA D₀ _ tp _ h.one_le_pre h.pre_le (fun hm => ?_) fun hm => ?_⟩
  · have hsmall : tPre31 c0 G N D₀ ≤ 20 * G.m₀ + 50 := by
      unfold tPre31 tLog4
      rw [if_pos hm]
      omega
    exact_mod_cast hsmall
  · have := hK N D₀ h.one_le_N hm (h.hyp hm)
    have : (0 : ℝ) ≤ ((20 * G.m₀ + 50 : ℕ) : ℝ) := by positivity
    linarith

/-! ### A query -/

/-- **The time of a query** is at most a constant times every bound tq ≥ 1 that, from the threshold
on, dominates the cost L ∑ α_d of Theorem 30. -/
theorem exists_tQuery31_le {C : ℝ} (hC : 0 ≤ C) : ∃ A : ℝ, 0 ≤ A ∧
    ∀ {N D₀ : ℕ} {tp tq : ℝ}, CostsWithin G C N D₀ tp tq → (tQuery31 G D₀ : ℝ) ≤ A * tq := by
  obtain ⟨K, hK0, hK⟩ := exists_tQueryAt_le
  obtain ⟨A, hA0, hA⟩ := exists_le_of_small_of_large G hC
    (S := ((40 * 4 ^ G.m₀ + 40 : ℕ) : ℝ)) (by positivity) hK0
  refine ⟨A, hA0, fun {N D₀ tp tq} h =>
    hA D₀ _ tq _ h.one_le_query h.query_le (fun hm => ?_) fun hm => ?_⟩
  · -- an inner product of D ≤ 4^m₀ summands
    have hD := (Nat.clog_le_iff_le_pow (by norm_num)).1 hm.le
    have hsmall : tQuery31 G D₀ ≤ 40 * 4 ^ G.m₀ + 40 := by
      unfold tQuery31 tIpAt
      rw [if_pos hm]
      omega
    exact_mod_cast hsmall
  · have hquery : (tQueryAt (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) : ℝ)
        ≤ K * G.queryCost D₀ :=
      hK (parOf G N D₀) (switchOf31 G D₀) (h.hyp hm)
    have htime :
        tQuery31 G D₀ = tQueryAt (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) + 20 := by
      unfold tQuery31
      rw [if_neg (not_lt.2 hm)]
    have h40 : (20 : ℝ) ≤ ((40 * 4 ^ G.m₀ + 40 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    rw [htime]
    push_cast at h40 ⊢
    linarith

end

/-- **The time of the offline routine**, with k further steps, is at most a constant times tp + w
tq, for all bounds tp, tq ≥ 1 that dominate the two costs of Theorem 30. -/
theorem exists_tOffline32_le (G : RatParams) {C : ℝ} (hC : 0 ≤ C) (c0 k : ℕ) : ∃ A : ℝ,
    ∀ {N D₀ : ℕ} {tp tq : ℝ} (w : ℕ), CostsWithin G C N D₀ tp tq →
      (tOffline32 c0 G N D₀ w : ℝ) + k ≤ A * (tp + w * tq) := by
  obtain ⟨Ap, hAp0, hAp⟩ := exists_tPre31_le G hC c0
  obtain ⟨Aq, hAq0, hAq⟩ := exists_tQuery31_le G hC
  refine ⟨(Ap + 20 + k) + (Aq + 30), fun {N D₀ tp tq} w h => ?_⟩
  have hpre := hAp h
  have hquery := hAq h
  have htp := h.one_le_pre
  have htq := h.one_le_query
  have hw : (0 : ℝ) ≤ (w : ℝ) := by positivity
  have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hwtq : 0 ≤ (w : ℝ) * tq := mul_nonneg hw (by linarith)
  have htime : (tOffline32 c0 G N D₀ w : ℝ)
      = (tPre31 c0 G N D₀ : ℝ) + (w : ℝ) * ((tQuery31 G D₀ : ℝ) + 30) + 20 := by
    simp only [tOffline32]
    push_cast
    ring
  -- the preprocessing and the k + 20 further steps against tp, the w queries against w tq
  have hfirst : (tPre31 c0 G N D₀ : ℝ) + 20 + k ≤ (Ap + 20 + k) * tp := by
    linarith [le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ 20 + (k : ℝ)) htp]
  have hsecond : (w : ℝ) * ((tQuery31 G D₀ : ℝ) + 30) ≤ (Aq + 30) * ((w : ℝ) * tq) := by
    calc (w : ℝ) * ((tQuery31 G D₀ : ℝ) + 30) ≤ (w : ℝ) * ((Aq + 30) * tq) :=
          mul_le_mul_of_nonneg_left (by linarith) hw
      _ = (Aq + 30) * ((w : ℝ) * tq) := by ring
  have hcross₁ : 0 ≤ (Ap + 20 + k) * ((w : ℝ) * tq) := mul_nonneg (by positivity) hwtq
  have hcross₂ : 0 ≤ (Aq + 30) * tp := mul_nonneg (by positivity) (by linarith)
  rw [htime]
  linarith

/-! ### Space and the nesting of calls -/







end Light.Sec4

end

end


-- Original source module: ThreeSumApsp.Programs.Sec4.ChoosingParameters.Setup
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Corollaries 26 and 31 in the light language: m, the places of the padded matrices, the query

m = ⌈log₄ D⌉ (`logFour`), the places of the padded matrices and of the block of Theorem 30 behind
the free pointer (`paddedXAt`, `paddedYAt`, `blockAt`), the text of the query, and the bounds on the
entries of the padded matrices. The text of the query serves all rational parameters; its
specification is `QuerySpec31`, proved in `query31_meets`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Parameters and map -/





/-! ## The query -/

namespace Query31









end Query31









/-- The ceiling ⌈log₄ D⌉ in natural numbers. -/
theorem ceil_logb_four (D₀ : ℕ) : ⌈Real.logb 4 (D₀ : ℝ)⌉₊ = logFour D₀ := by
  have := Real.natCeil_logb_natCast 4 D₀
  simpa [logFour] using this





end Light.Sec4

end

end


-- Original source module: ThreeSumApsp.Util.Log
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Logarithms and real powers

Small facts on `Real.log`, `Real.logb`, `Nat.clog`, `Real.sqrt` and real powers that the estimates
of the paper use silently.

* Values, in the namespace `Real` and named by Mathlib's convention: `1 / 2 < log 2 < 1`,
  `log 4 = 2 log 2`, `log 9 = 2 log 3`, `1 ≤ log 4`, `1 / 2 ≤ log x` for `x ≥ 2`, `1 ≤ log x` for
  `x ≥ 3`, `log₂ 7 < 2.81`, `4 ≤ √D` for `D ≥ 16`.
* The rounded logarithm: `⌈log_b n⌉ < log_b n + 1` (`Real.natCast_clog_lt_logb_add_one`),
  `c ^ ⌈log_b n⌉ ≤ c * n ^ (log_b c)` (`Real.pow_clog_le_mul_rpow_logb`).
* The definition `logU u = log (max u 2)`, the paper's `log U`.
-/

@[expose] public section

namespace Real

/-! ### Values -/





/-- `log 4 = 2 log 2`. -/
theorem log_four : log 4 = 2 * log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow, Nat.cast_ofNat]

/-- `log 9 = 2 log 3`. -/
theorem log_nine : log 9 = 2 * log 3 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, log_pow, Nat.cast_ofNat]

/-- `1 ≤ log 4`. -/
theorem one_le_log_four : 1 ≤ log 4 := by
  linarith [log_four, one_half_lt_log_two]











/-! ### The rounded logarithm `Nat.clog` -/





end Real

namespace ThreeSumApsp



end ThreeSumApsp

end

end


-- Original source module: ThreeSumApsp.Sec4.ChoosingParameters
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# 4.4 Choosing the parameters: the entropy function, the exponents `γ` and `q`, equation (11)

Section 4.4 chooses the parameters `L` and `t` of Theorem 30. This file has the facts that its
proofs use about `D = 4^m` and about the notions with which Corollary 31 is stated ("Other choices
of the parameters"). The notation of the paper: `entropy` is `H`, `rhoC c` is `ρ_c = 9/(c-1)`,
`gammaOf c θ` is `γ = θ ln(1/ρ_c)/ln 4`, `qOf θ` is `q = (H(θ) + θ ln 9)/ln 4`, `lnΛ c γ` is the
denominator `ln Λ` of (11), `Rc c γ` is `R_c(γ) = ln 4/ln Λ`, and `D m` is `D = 4^m`.

* The entropy function `H` is Mathlib's `Real.binEntropy` (`entropy_eq_binEntropy`); continuity,
  concavity and the derivative come from there.
* Powers and logarithms of `D = 4^m` (`cast_D_pos`, `one_le_cast_D`, `log_cast_D`,
  `cast_le_log_cast_D`, `cast_D_rpow`).
* The bound `binom(n, k) ≥ e^{n H(k/n)}/(n+1)` (`exp_entropy_div_le_choose`): it is the standard
  bound `binom(n, k) ≥ 1/(n+1) · n^n/(k^k (n-k)^{n-k})`, as `e^{n H(k/n)} = n^n/(k^k (n-k)^{n-k})`.
* One section for each of `ρ_c`, `γ`, `q`, and `ln Λ` with `R_c(γ)`: signs, monotonicity and
  continuity, and the three facts that tie them to the costs: `ρ_c^{θm} = D^{-γ}`
  (`rhoC_rpow_eq_D_rpow`), `e^{m(H(θ) + θ ln 9)} = D^q` (`exp_entropy_eq_D_rpow_qOf`), and
  `Λ < 4^{1/ε}` if and only if `ε < R_c(γ)` (`eq_11_iff`).
-/

public section

open Finset

namespace ThreeSumApsp

/-! ### The entropy function: the link with Mathlib's `Real.binEntropy` -/















/-! ### Powers and logarithms of `D = 4^m` -/

/-- `ln 4 > 0`. -/
theorem log_four_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)

/-- `D = 4^m` as a real number. -/
theorem cast_D_eq (m : ℕ) : (D m : ℝ) = (4 : ℝ) ^ m := by
  simp [D]

/-- `D > 0`. -/
theorem cast_D_pos (m : ℕ) : (0 : ℝ) < (D m : ℝ) := by
  rw [cast_D_eq]
  positivity

/-- `D ≥ 1`. -/
theorem one_le_cast_D (m : ℕ) : (1 : ℝ) ≤ (D m : ℝ) := by
  rw [cast_D_eq]
  exact one_le_pow₀ (by norm_num)

/-- `ln D = m ln 4`. -/
theorem log_cast_D (m : ℕ) : Real.log (D m : ℝ) = (m : ℝ) * Real.log 4 := by
  rw [cast_D_eq, Real.log_pow]

/-- `m ≤ ln D`. -/
theorem cast_le_log_cast_D (m : ℕ) : (m : ℝ) ≤ Real.log (D m : ℝ) := by
  rw [log_cast_D]
  exact le_mul_of_one_le_right (Nat.cast_nonneg m) Real.one_le_log_four

/-- `D^x = e^{x m ln 4}`. -/
theorem cast_D_rpow (m : ℕ) (x : ℝ) :
    (D m : ℝ) ^ x = Real.exp (x * ((m : ℝ) * Real.log 4)) := by
  rw [Real.rpow_def_of_pos (cast_D_pos m), log_cast_D]
  ring_nf

/-! ### The lower bound on binomial coefficients by the entropy function -/







/-! ### The decay rate `ρ_c` -/

/-- `ρ_c = 9/(c-1) > 0` for `c > 10`. -/
theorem rhoC_pos {c : ℝ} (hc : 10 < c) : 0 < rhoC c := div_pos (by norm_num) (by linarith)









/-! ### The exponent `γ` -/

/-- `γ` is proportional to `θ`. -/
theorem gammaOf_eq_mul (c θ : ℝ) : gammaOf c θ = θ * gammaOf c 1 := by
  unfold gammaOf
  ring







/-- Proof of Corollary 31: "ρ_c^{θm} = D^{-γ}", with `D = 4^m` and `γ = θ ln(1/ρ_c)/ln 4`. -/
theorem rhoC_rpow_eq_D_rpow (c θ : ℝ) (hc : 10 < c) (m : ℕ) :
    rhoC c ^ (θ * (m : ℝ)) = (D m : ℝ) ^ (-gammaOf c θ) := by
  rw [cast_D_rpow, Real.rpow_def_of_pos (rhoC_pos hc)]
  congr 1
  have hfour := log_four_pos.ne'
  unfold gammaOf
  rw [one_div, Real.log_inv]
  field_simp

/-! ### The exponent `q` -/













/-- `e^{m(H(θ) + θ ln 9)} = D^q` with `D = 4^m` and `q = (H(θ) + θ ln 9)/ln 4`. -/
theorem exp_entropy_eq_D_rpow_qOf (θ : ℝ) (m : ℕ) :
    Real.exp ((m : ℝ) * (entropy θ + θ * Real.log 9)) = (D m : ℝ) ^ qOf θ := by
  rw [cast_D_rpow]
  congr 1
  have hfour := log_four_pos.ne'
  unfold qOf
  field_simp

/-! ### The denominator `ln Λ` of equation (11), and `R_c(γ)` -/











end ThreeSumApsp

end

end


-- Original source module: ThreeSumApsp.Sec4.ParameterSteps
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


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

/-- Proof of Corollary 26, "Setting up": for "m := ⌈log_4 D⌉" and `D ≥ 2` the padded inner dimension
satisfies `D ≤ 4^m` and "4^m < 4D", and "the original D was larger than 4^{m-1}". -/
theorem Corollary26.setting_up (D₀ m : ℕ) (hD : 2 ≤ D₀) (hm : m = ⌈Real.logb 4 (D₀ : ℝ)⌉₊) :
    D₀ ≤ D m ∧ D m < 4 * D₀ ∧ 4 ^ (m - 1) < D₀ := by
  obtain rfl : m = Nat.clog 4 D₀ := by
    rw [hm, ← Real.natCeil_logb_natCast]
    norm_num
  have hpos : 1 ≤ Nat.clog 4 D₀ := Nat.clog_pos (by norm_num) hD
  have hlt : 4 ^ (Nat.clog 4 D₀ - 1) < D₀ := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hsucc : 4 ^ Nat.clog 4 D₀ = 4 * 4 ^ (Nat.clog 4 D₀ - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  refine ⟨Nat.le_pow_clog (by norm_num) _, ?_, hlt⟩
  unfold D
  omega







/-- The padded inner dimension is at least the given one. -/
theorem Sizes.SetUp.le {p : Sizes} (h : p.SetUp) : p.D₀ ≤ D p.m :=
  (Corollary26.setting_up p.D₀ p.m h.two_le h.m_eq).1

/-- "4^m < 4D". -/
theorem Sizes.SetUp.lt {p : Sizes} (h : p.SetUp) : D p.m < 4 * p.D₀ :=
  (Corollary26.setting_up p.D₀ p.m h.two_le h.m_eq).2.1

/-- "the original D was larger than 4^{m-1}". -/
theorem Sizes.SetUp.gt {p : Sizes} (h : p.SetUp) : 4 ^ (p.m - 1) < p.D₀ :=
  (Corollary26.setting_up p.D₀ p.m h.two_le h.m_eq).2.2



/-- Proof of Corollary 26, "Setting up": padding "changes D by a factor less than 4, which only
affects the constants". A bound `D^a log^k D` in the padded `D = 4^m` is, up to a constant, the same
bound in the original inner dimension `D₀`. (Corollary 26 has `k = 0`; the bounds of Corollary 31
have logarithms.) -/
theorem padded_le (a : ℝ) (k : ℕ) :
    Dominated Sizes.SetUp (fun p => (D p.m : ℝ) ^ a * Real.log (D p.m) ^ k)
      fun p => (p.D₀ : ℝ) ^ a * Real.log p.D₀ ^ k := by
  refine .of_le_const_mul (C := 4 ^ |a| * 3 ^ k) (by positivity) fun ⟨D₀, _, m⟩ h => ?_
  have htwo : (2 : ℝ) ≤ D₀ := by exact_mod_cast h.two_le
  have hD₀ : (0 : ℝ) < D₀ := by linarith
  have hle' : 1 ≤ (D m : ℝ) / D₀ := (one_le_div hD₀).2 (by exact_mod_cast h.le)
  have hle4 : (D m : ℝ) ≤ 4 * D₀ := by exact_mod_cast h.lt.le
  have hpow : (D m : ℝ) ^ a ≤ 4 ^ |a| * (D₀ : ℝ) ^ a :=
    calc (D m : ℝ) ^ a = ((D m : ℝ) / D₀) ^ a * (D₀ : ℝ) ^ a := by
          rw [← Real.mul_rpow (by positivity) hD₀.le, div_mul_cancel₀ _ hD₀.ne']
      _ ≤ 4 ^ |a| * (D₀ : ℝ) ^ a :=
          mul_le_mul_of_nonneg_right
            ((Real.rpow_le_rpow_of_exponent_le hle' (le_abs_self a)).trans
              (Real.rpow_le_rpow (by positivity) ((div_le_iff₀ hD₀).2 hle4) (abs_nonneg a)))
            (by positivity)
  have hlog : Real.log (D m) ≤ 3 * Real.log D₀ :=
    calc Real.log (D m) ≤ Real.log (4 * D₀) := Real.log_le_log (cast_D_pos m) hle4
      _ = 2 * Real.log 2 + Real.log D₀ := by
          rw [Real.log_mul (by norm_num) hD₀.ne', Real.log_four]
      _ ≤ 3 * Real.log D₀ := by linarith [Real.log_le_log two_pos htwo]
  calc (D m : ℝ) ^ a * Real.log (D m) ^ k
      ≤ 4 ^ |a| * (D₀ : ℝ) ^ a * (3 * Real.log D₀) ^ k :=
        mul_le_mul hpow (pow_le_pow_left₀ (by positivity) hlog k) (by positivity) (by positivity)
    _ = 4 ^ |a| * 3 ^ k * ((D₀ : ℝ) ^ a * Real.log D₀ ^ k) := by
        rw [mul_pow]
        ring



/-- The hypothesis `t ≤ m` of Theorem 30 holds for `t = ⌈θm⌉` with `θ ≤ 1`. -/
theorem switchOf_le {θ : ℝ} (hθ : θ ≤ 1) (m : ℕ) : switchOf θ m ≤ m :=
  Nat.ceil_le.2 (mul_le_of_le_one_left (Nat.cast_nonneg m) hθ)

/-! ### Queries -/

/-- Proof of Corollary 26, "Queries": "A query reads ∑_{d≤t} α_d numbers, and we bound this sum as
in the proof of Lemma 11. Since 9^d = 72^d 8^{-d} ≤ 72^t 8^{-d} for d ≤ t", the sum `∑_{d ≤ t} α_d`
is at most `72^t ∑_{d=0}^{m} binom(m, d) 8^{-d} = 72^t (9/8)^m`. Here any `x > 0` with `9x ≥ 1`
stands for 8, because the proof of Corollary 31 makes "the same calculation with x := (1-θ)/θ in
place of 8". -/
theorem sum_alpha_le {x : ℝ} (hx : 0 < x) (h9x : 1 ≤ 9 * x) {m t : ℕ} (htm : t ≤ m) :
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

/-- `(9x)^{θm} (1+1/x)^m = D^q` for "x := (1-θ)/θ". -/
theorem rpow_mul_pow_eq_D_rpow_qOf {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (m : ℕ) :
    (9 * ((1 - θ) / θ)) ^ (θ * (m : ℝ)) * (1 + 1 / ((1 - θ) / θ)) ^ m = (D m : ℝ) ^ qOf θ := by
  have h1θ : 0 < 1 - θ := sub_pos.2 hθ1
  have hinv : 1 + 1 / ((1 - θ) / θ) = (1 - θ)⁻¹ := by
    field_simp
    ring
  rw [← exp_entropy_eq_D_rpow_qOf, hinv, Real.rpow_def_of_pos (by positivity),
    ← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity), ← Real.exp_add, Real.log_inv,
    Real.log_mul (by norm_num) (by positivity), Real.log_div h1θ.ne' hθ0.ne', entropy]
  congr 1
  ring

/-! ### Encodings -/



/-- Proof of Corollary 26: (10) implies "that the last term of (8) is at most N²/D^γ", "by
rearranging". -/
theorem Equation10.last_term {L m N : ℕ} {γ : ℝ} (h10 : lhs10 L m γ ≤ N) :
    (N : ℝ) * (10 : ℝ) ^ L / sqrtKN0 L m ≤ (N : ℝ) ^ 2 / (D m : ℝ) ^ γ := by
  rw [le_div_iff₀ (Real.rpow_pos_of_pos (cast_D_pos m) γ)]
  calc (N : ℝ) * (10 : ℝ) ^ L / sqrtKN0 L m * (D m : ℝ) ^ γ
      = (N : ℝ) * lhs10 L m γ := by rw [lhs10]; ring
    _ ≤ (N : ℝ) * (N : ℝ) := mul_le_mul_of_nonneg_left h10 (Nat.cast_nonneg N)
    _ = (N : ℝ) ^ 2 := (sq _).symm

/-- Proof of Corollary 26: (10) implies "that N ≥ √K N₀", "because 10^L ≥ M = K N₀² and D^γ ≥ 1"
(here `γ ≥ 0`). -/
theorem Equation10.tile_fits {L m N : ℕ} (hmL : m ≤ L) {γ : ℝ} (hγ : 0 ≤ γ)
    (h10 : lhs10 L m γ ≤ N) : sqrtKN0 L m ≤ N := by
  have hpos := sqrtKN0_pos hmL
  have hM : sqrtKN0 L m ^ 2 ≤ (10 : ℝ) ^ L := by
    rw [sqrtKN0_sq]
    exact_mod_cast M_le_ten_pow L m
  have hD1 : 1 ≤ (D m : ℝ) ^ γ := Real.one_le_rpow (one_le_cast_D m) hγ
  calc sqrtKN0 L m = sqrtKN0 L m ^ 2 / sqrtKN0 L m := by field_simp
    _ ≤ (10 : ℝ) ^ L / sqrtKN0 L m := div_le_div_of_nonneg_right hM hpos.le
    _ ≤ lhs10 L m γ :=
        div_le_div_of_nonneg_right (le_mul_of_one_le_left (by positivity) hD1) hpos.le
    _ ≤ (N : ℝ) := h10

/-! ### Conclusion -/

/-- The expression (8) from its two terms, with `L` and `t` given as functions of `m`. If the first
term, without its factor `N²`, is `O(G)`, where `G ≥ D^{-γ}`, then (8) is `O(G N²)` wherever (10)
holds. -/
theorem dominated_cost8_of_eq_10 {Lof tof : ℕ → ℕ} {γ : ℝ} {G : ℕ → ℝ} {domM : ℕ → Prop}
    {dom : Sizes → Prop}
    (hfirst : Dominated domM
      (fun m => (Lof m : ℝ) * m * (rho (Lof m) m ^ tof m / (1 - rho (Lof m) m))) G)
    (hdom : ∀ p, dom p → domM p.m) (hG : ∀ p, dom p → (D p.m : ℝ) ^ (-γ) ≤ G p.m)
    (h10 : ∀ p, dom p → lhs10 (Lof p.m) p.m γ ≤ p.N) :
    Dominated dom (fun p => cost8 (Lof p.m) p.m (tof p.m) p.N) fun p => G p.m * (p.N : ℝ) ^ 2 := by
  -- the first term of (8), with its factor `N²`
  have hboxes := (hfirst.comp Sizes.m hdom).mul_right (k := fun p => (p.N : ℝ) ^ 2)
    fun _ _ => sq_nonneg _
  -- the last term
  have hencodings : Dominated dom
      (fun p => (p.N : ℝ) * (10 : ℝ) ^ Lof p.m / sqrtKN0 (Lof p.m) p.m)
      fun p => G p.m * (p.N : ℝ) ^ 2 :=
    .of_le fun p hp => (Equation10.last_term (h10 p hp)).trans <| by
      rw [div_eq_mul_inv, mul_comm, ← Real.rpow_neg (cast_D_pos p.m).le]
      exact mul_le_mul_of_nonneg_right (hG p hp) (sq_nonneg _)
  exact hboxes.add hencodings

end ThreeSumApsp

end

end


-- Original source module: ThreeSumApsp.Sec4.Table2.LogBounds
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


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









/-- A lower bound on `ln 10 = 2.302585092994…`. -/
noncomputable def logTenLo : ℝ := 2.3025850922

/-- An upper bound on `ln 10 = 2.302585092994…`. -/
noncomputable def logTenHi : ℝ := 2.3025850938









private lemma log_two_mem : Real.log 2 ∈ Set.Icc logTwoLo logTwoHi :=
  ⟨Real.log_two_gt_d9.le, Real.log_two_lt_d9.le⟩

/-- The enclosure of `log θ`, between two rational numbers if `θ` is rational. It holds for every
`k` and `n`; they decide only how tight it is. -/
theorem log_mem (k : ℤ) (n : ℕ) {θ : ℝ} (hθ : 0 < θ := by ((norm_num [_root_.ThreeSumApsp.logApprox, _root_.ThreeSumApsp.logErr, _root_.ThreeSumApsp.seriesArg,
                                                               _root_.ThreeSumApsp.logTwoLo, _root_.ThreeSumApsp.logTwoHi, _root_.ThreeSumApsp.logThreeLo,
                                                               _root_.ThreeSumApsp.logThreeHi, _root_.ThreeSumApsp.logTenLo, _root_.ThreeSumApsp.logTenHi,
                                                               _root_.Finset.sum_range_succ, _root_.ThreeSumApsp.rhoC])
                                                                 )) :
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

private lemma log_three_mem : Real.log 3 ∈ Set.Icc logThreeLo logThreeHi :=
  ⟨le_trans (by ((norm_num [_root_.ThreeSumApsp.logApprox, _root_.ThreeSumApsp.logErr, _root_.ThreeSumApsp.seriesArg,
                     _root_.ThreeSumApsp.logTwoLo, _root_.ThreeSumApsp.logTwoHi, _root_.ThreeSumApsp.logThreeLo,
                     _root_.ThreeSumApsp.logThreeHi, _root_.ThreeSumApsp.logTenLo, _root_.ThreeSumApsp.logTenHi,
                     _root_.Finset.sum_range_succ, _root_.ThreeSumApsp.rhoC])
                       )) (log_mem 2 7).1, (log_mem 2 7).2.trans (by ((norm_num [_root_.ThreeSumApsp.logApprox, _root_.ThreeSumApsp.logErr, _root_.ThreeSumApsp.seriesArg,
                                                                          _root_.ThreeSumApsp.logTwoLo, _root_.ThreeSumApsp.logTwoHi, _root_.ThreeSumApsp.logThreeLo,
                                                                          _root_.ThreeSumApsp.logThreeHi, _root_.ThreeSumApsp.logTenLo, _root_.ThreeSumApsp.logTenHi,
                                                                          _root_.Finset.sum_range_succ, _root_.ThreeSumApsp.rhoC])
                                                                            ))⟩



/-! ## The exponent `q` of the query time (Corollary 31) -/

/-- `q(θ)` written out in terms of `log 2` and `log 3`. -/
private lemma qOf_eq_div (θ : ℝ) :
    qOf θ = (-θ * Real.log θ - (1 - θ) * Real.log (1 - θ) + θ * (2 * Real.log 3))
      / (2 * Real.log 2) := by
  unfold qOf entropy
  rw [Real.log_four, Real.log_nine]

/-- An upper bound on `q(θ)` at a rational `θ`. The hypothesis `h` is `H(θ) + θ ln 9 ≤ r ln 4` with
every logarithm replaced by the bound that makes the inequality harder. Here `2^k` is the power of
two nearest to `θ`; four terms of the series for `log θ` and for `log (1 - θ)` are enough for every
entry of Table 2. -/
theorem qOf_le (k : ℤ) {θ r : ℝ} (h0 : 0 < θ := by ((norm_num [_root_.ThreeSumApsp.logApprox, _root_.ThreeSumApsp.logErr, _root_.ThreeSumApsp.seriesArg,
                                                        _root_.ThreeSumApsp.logTwoLo, _root_.ThreeSumApsp.logTwoHi, _root_.ThreeSumApsp.logThreeLo,
                                                        _root_.ThreeSumApsp.logThreeHi, _root_.ThreeSumApsp.logTenLo, _root_.ThreeSumApsp.logTenHi,
                                                        _root_.Finset.sum_range_succ, _root_.ThreeSumApsp.rhoC])
                                                          )) (h1 : θ < 1 := by ((norm_num [_root_.ThreeSumApsp.logApprox, _root_.ThreeSumApsp.logErr, _root_.ThreeSumApsp.seriesArg,
                                                                                    _root_.ThreeSumApsp.logTwoLo, _root_.ThreeSumApsp.logTwoHi, _root_.ThreeSumApsp.logThreeLo,
                                                                                    _root_.ThreeSumApsp.logThreeHi, _root_.ThreeSumApsp.logTenLo, _root_.ThreeSumApsp.logTenHi,
                                                                                    _root_.Finset.sum_range_succ, _root_.ThreeSumApsp.rhoC])
                                                                                      ))
    (hr : 0 ≤ r := by ((norm_num [_root_.ThreeSumApsp.logApprox, _root_.ThreeSumApsp.logErr, _root_.ThreeSumApsp.seriesArg,
                           _root_.ThreeSumApsp.logTwoLo, _root_.ThreeSumApsp.logTwoHi, _root_.ThreeSumApsp.logThreeLo,
                           _root_.ThreeSumApsp.logThreeHi, _root_.ThreeSumApsp.logTenLo, _root_.ThreeSumApsp.logTenHi,
                           _root_.Finset.sum_range_succ, _root_.ThreeSumApsp.rhoC])
                             ))
    (h : -θ * (logApprox k 4 θ - logErr k 4 θ)
        - (1 - θ) * (logApprox 0 4 (1 - θ) - logErr 0 4 (1 - θ)) + θ * (2 * logThreeHi)
      ≤ r * (2 * logTwoLo) := by ((norm_num [_root_.ThreeSumApsp.logApprox, _root_.ThreeSumApsp.logErr, _root_.ThreeSumApsp.seriesArg,
                                      _root_.ThreeSumApsp.logTwoLo, _root_.ThreeSumApsp.logTwoHi, _root_.ThreeSumApsp.logThreeLo,
                                      _root_.ThreeSumApsp.logThreeHi, _root_.ThreeSumApsp.logTenLo, _root_.ThreeSumApsp.logTenHi,
                                      _root_.Finset.sum_range_succ, _root_.ThreeSumApsp.rhoC])
                                        )) : qOf θ ≤ r := by
  have hcompl : 0 < 1 - θ := sub_pos.2 h1
  rw [qOf_eq_div, div_le_iff₀ (mul_pos two_pos (Real.log_pos one_lt_two))]
  have hlog := mul_le_mul_of_nonneg_left (log_mem k 4 h0).1 h0.le
  have hlogc := mul_le_mul_of_nonneg_left (log_mem 0 4 hcompl).1 hcompl.le
  have hthree := mul_le_mul_of_nonneg_left log_three_mem.2 h0.le
  have htwo := mul_le_mul_of_nonneg_left log_two_mem.1 hr
  linarith [h, hlog, hlogc, hthree, htwo]

/-- A lower bound on `q(θ)` at a rational `θ`, computed as in `qOf_le`. -/
theorem le_qOf (k : ℤ) {θ r : ℝ} (h0 : 0 < θ := by ((norm_num [_root_.ThreeSumApsp.logApprox, _root_.ThreeSumApsp.logErr, _root_.ThreeSumApsp.seriesArg,
                                                        _root_.ThreeSumApsp.logTwoLo, _root_.ThreeSumApsp.logTwoHi, _root_.ThreeSumApsp.logThreeLo,
                                                        _root_.ThreeSumApsp.logThreeHi, _root_.ThreeSumApsp.logTenLo, _root_.ThreeSumApsp.logTenHi,
                                                        _root_.Finset.sum_range_succ, _root_.ThreeSumApsp.rhoC])
                                                          )) (h1 : θ < 1 := by ((norm_num [_root_.ThreeSumApsp.logApprox, _root_.ThreeSumApsp.logErr, _root_.ThreeSumApsp.seriesArg,
                                                                                    _root_.ThreeSumApsp.logTwoLo, _root_.ThreeSumApsp.logTwoHi, _root_.ThreeSumApsp.logThreeLo,
                                                                                    _root_.ThreeSumApsp.logThreeHi, _root_.ThreeSumApsp.logTenLo, _root_.ThreeSumApsp.logTenHi,
                                                                                    _root_.Finset.sum_range_succ, _root_.ThreeSumApsp.rhoC])
                                                                                      ))
    (hr : 0 ≤ r := by ((norm_num [_root_.ThreeSumApsp.logApprox, _root_.ThreeSumApsp.logErr, _root_.ThreeSumApsp.seriesArg,
                           _root_.ThreeSumApsp.logTwoLo, _root_.ThreeSumApsp.logTwoHi, _root_.ThreeSumApsp.logThreeLo,
                           _root_.ThreeSumApsp.logThreeHi, _root_.ThreeSumApsp.logTenLo, _root_.ThreeSumApsp.logTenHi,
                           _root_.Finset.sum_range_succ, _root_.ThreeSumApsp.rhoC])
                             ))
    (h : r * (2 * logTwoHi)
      ≤ -θ * (logApprox k 4 θ + logErr k 4 θ)
        - (1 - θ) * (logApprox 0 4 (1 - θ) + logErr 0 4 (1 - θ)) + θ * (2 * logThreeLo) := by
      ((norm_num [_root_.ThreeSumApsp.logApprox, _root_.ThreeSumApsp.logErr, _root_.ThreeSumApsp.seriesArg,
           _root_.ThreeSumApsp.logTwoLo, _root_.ThreeSumApsp.logTwoHi, _root_.ThreeSumApsp.logThreeLo,
           _root_.ThreeSumApsp.logThreeHi, _root_.ThreeSumApsp.logTenLo, _root_.ThreeSumApsp.logTenHi,
           _root_.Finset.sum_range_succ, _root_.ThreeSumApsp.rhoC])
             )) : r ≤ qOf θ := by
  have hcompl : 0 < 1 - θ := sub_pos.2 h1
  rw [qOf_eq_div, le_div_iff₀ (mul_pos two_pos (Real.log_pos one_lt_two))]
  have hlog := mul_le_mul_of_nonneg_left (log_mem k 4 h0).2 h0.le
  have hlogc := mul_le_mul_of_nonneg_left (log_mem 0 4 hcompl).2 hcompl.le
  have hthree := mul_le_mul_of_nonneg_left log_three_mem.1 h0.le
  have htwo := mul_le_mul_of_nonneg_left log_two_mem.2 hr
  linarith [h, hlog, hlogc, hthree, htwo]

/-! ## The exponent `γ` (Corollary 31) -/

/-- Bounds on `γ` at `θ = 1`, that is on `ln(1/ρ_c)/ln 4`, from bounds on `ln(1/ρ_c)`. -/
theorem gammaOf_one_mem {c a b glo ghi : ℝ} (h : Real.log (1 / rhoC c) ∈ Set.Icc a b)
    (hglo : 0 ≤ glo := by ((norm_num [_root_.ThreeSumApsp.logApprox, _root_.ThreeSumApsp.logErr, _root_.ThreeSumApsp.seriesArg,
                               _root_.ThreeSumApsp.logTwoLo, _root_.ThreeSumApsp.logTwoHi, _root_.ThreeSumApsp.logThreeLo,
                               _root_.ThreeSumApsp.logThreeHi, _root_.ThreeSumApsp.logTenLo, _root_.ThreeSumApsp.logTenHi,
                               _root_.Finset.sum_range_succ, _root_.ThreeSumApsp.rhoC])
                                 )) (hghi : 0 ≤ ghi := by ((norm_num [_root_.ThreeSumApsp.logApprox, _root_.ThreeSumApsp.logErr, _root_.ThreeSumApsp.seriesArg,
                                                               _root_.ThreeSumApsp.logTwoLo, _root_.ThreeSumApsp.logTwoHi, _root_.ThreeSumApsp.logThreeLo,
                                                               _root_.ThreeSumApsp.logThreeHi, _root_.ThreeSumApsp.logTenLo, _root_.ThreeSumApsp.logTenHi,
                                                               _root_.Finset.sum_range_succ, _root_.ThreeSumApsp.rhoC])
                                                                 ))
    (hlo : glo * (2 * logTwoHi) ≤ a := by ((norm_num [_root_.ThreeSumApsp.logApprox, _root_.ThreeSumApsp.logErr, _root_.ThreeSumApsp.seriesArg,
                                               _root_.ThreeSumApsp.logTwoLo, _root_.ThreeSumApsp.logTwoHi, _root_.ThreeSumApsp.logThreeLo,
                                               _root_.ThreeSumApsp.logThreeHi, _root_.ThreeSumApsp.logTenLo, _root_.ThreeSumApsp.logTenHi,
                                               _root_.Finset.sum_range_succ, _root_.ThreeSumApsp.rhoC])
                                                 ))
    (hhi : b ≤ ghi * (2 * logTwoLo) := by ((norm_num [_root_.ThreeSumApsp.logApprox, _root_.ThreeSumApsp.logErr, _root_.ThreeSumApsp.seriesArg,
                                               _root_.ThreeSumApsp.logTwoLo, _root_.ThreeSumApsp.logTwoHi, _root_.ThreeSumApsp.logThreeLo,
                                               _root_.ThreeSumApsp.logThreeHi, _root_.ThreeSumApsp.logTenLo, _root_.ThreeSumApsp.logTenHi,
                                               _root_.Finset.sum_range_succ, _root_.ThreeSumApsp.rhoC])
                                                 )) : gammaOf c 1 ∈ Set.Icc glo ghi := by
  have hpos : 0 < 2 * Real.log 2 := mul_pos two_pos (Real.log_pos one_lt_two)
  have htwolo := mul_le_mul_of_nonneg_left log_two_mem.2 hglo
  have htwohi := mul_le_mul_of_nonneg_left log_two_mem.1 hghi
  rw [Set.mem_Icc, gammaOf, Real.log_four, one_mul, le_div_iff₀ hpos, div_le_iff₀ hpos]
  exact ⟨by linarith [hlo, htwolo, h.1], by linarith [hhi, htwohi, h.2]⟩



/-! ## The bound `R_c(γ)` (equation (11)) -/







/-! ## Entries of Table 2

An entry needs two facts on its row, `hg` (an enclosure of `ln(1/ρ_c)/ln 4`) and `hR` (the `ε` of
the row is below `R_c(γ)` up to the largest `γ` of the row), and two rational numbers `θlo ≤ θhi`
that enclose its `θ`. -/













end ThreeSumApsp

end

end


-- Original source module: ThreeSumApsp.Sec4.Table2
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Table 2

Section 4.4 prescribes how an entry is computed. The left half has the `γ` of Corollary 31, "with
the c of the row and the θ that gives the q of the column (θ = 1/9 for q = 0.43)". The right half
has the `γ` of Corollary 32, "with the θ at which γ = κ - q". "The ε of a row of the table is the
smallest R_c(γ) over its entries." All values are rounded down (caption).

* The `θ` of a column of the left half does not depend on the row. It is enclosed between two
  decimal numbers (`exists_qOf_eq_010` to `exists_qOf_eq_090`): `q(θ)` is at most the `q` of the
  column at the lower number (`qOf_le`) and at least that `q` at the upper number (`le_qOf`), and it
  is continuous.
* A row (`table_2_c40` to `table_2_c10_5`) depends on `c` through two numbers: `ln(1/ρ_c)/ln 4`, by
  which `θ` is multiplied to give `γ` (`hg`), and the denominator of (11) at `γ = 0` (`hB`), which
  gives `ε < R_c(γ)` for every `γ` up to the largest one of the row (`hR`).
* An entry of the left half is `Table2Query.intro` at the enclosure of the `θ` of its column. An
  entry of the right half (`Table2Density.intro`) names two decimal numbers: at the lower one
  `γ + q ≤ κ` (`qOf_le`), at the upper one `γ + q ≥ κ` (`le_qOf`), so the root `θ` of `γ + q = κ`
  lies between them; and `γ = θ ln(1/ρ_c)/ln 4` has the printed four decimals at both.

How to read the numbers in the proofs. The two decimal numbers around a `θ` are `θ` cut after five
decimals and the next such number, or after six decimals where `γ` is too close to a multiple of
`0.0001`. The argument `k` of `qOf_le`, `le_qOf` and `log_mem` is the exponent of the power of two
nearest to the number whose logarithm is taken, and the second argument of `log_mem` is the number
of terms of the series.
-/

public section

open Finset

namespace ThreeSumApsp

/-! ## The `θ` of the columns of the left half -/











/-- Caption of Table 2: at `θ = 1/9`, "more precisely, q = 0.4277…". -/
theorem qOf_ninth_mem : qOf (1 / 9) ∈ Set.Icc 0.42773 0.42774 :=
  ⟨le_qOf (-3), qOf_le (-3)⟩

/-! ## The six rows -/



/-- `ln(1/ρ_c)/ln 4` for `c = 21` (the proof of Corollary 26 uses it too). -/
theorem gammaOf_21_one_mem : gammaOf 21 1 ∈ Set.Icc 0.576001 0.576002 :=
  gammaOf_one_mem (log_mem 1 3)

















end ThreeSumApsp

end

end


-- Original source module: ThreeSumApsp.Util.Asymptotics.Logarithms
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Logarithms up to a constant factor

Bounds on logarithms in the calculus `Dominated`, for every argument of a domain and not only for
large ones.

* Absorbing logarithms, for `x ≥ 1`: `(log x + 1) ^ e` is `O(x ^ η)` for `η > 0`
  (`dominated_log_add_one_pow_rpow`), hence `x ^ a * (log x) ^ e = O(x ^ b)` for `a < b`
  (`dominated_rpow_mul_log_pow_rpow`).
* From 2 on: `log x + 1 = O(log x)` (`dominated_log_add_one_log`) and `⌈log_b n⌉ + 1 = O(log n)`
  (`dominated_clog_add_one_log`).

For a natural number or a field of a parameter record in place of `x`, use `Dominated.comp`.
-/

public section

namespace ThreeSumApsp

open Real

/-! ### Absorbing logarithms, for all `x ≥ 1` -/

/-- `log x + 1 = O(x ^ η)` on `x ≥ 1`, for `η > 0`. -/
theorem dominated_log_add_one_rpow {η : ℝ} (hη : 0 < η) :
    Dominated (fun x : ℝ => 1 ≤ x) (fun x => log x + 1) fun x => x ^ η := by
  refine .of_le_const_mul (C := 1 / η + 1) (by positivity) fun x hx => ?_
  have hlog : log x ≤ x ^ η / η := log_le_rpow_div (zero_le_one.trans hx) hη
  have hone : 1 ≤ x ^ η := one_le_rpow hx hη.le
  rw [add_mul, one_mul, one_div_mul_eq_div]
  exact add_le_add hlog hone

/-- `(log x + 1) ^ e = O(x ^ η)` on `x ≥ 1`, for `η > 0`. -/
theorem dominated_log_add_one_pow_rpow {η : ℝ} (hη : 0 < η) (e : ℕ) :
    Dominated (fun x : ℝ => 1 ≤ x) (fun x => (log x + 1) ^ e) fun x => x ^ η := by
  have hstep := (dominated_log_add_one_rpow (div_pos hη (Nat.cast_add_one_pos e))).pow
    (fun x hx => add_nonneg (log_nonneg hx) zero_le_one) e
  refine hstep.mono_right fun x hx => ?_
  rw [← rpow_natCast, ← rpow_mul (zero_le_one.trans hx)]
  refine rpow_le_rpow_of_exponent_le hx ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ (Nat.cast_add_one_pos e)]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hη.le

/-- Logarithms are absorbed: `x ^ a * (log x + 1) ^ e = O(x ^ b)` on `x ≥ 1`, for `a < b`. -/
theorem dominated_rpow_mul_log_add_one_pow_rpow {a b : ℝ} (hab : a < b) (e : ℕ) :
    Dominated (fun x : ℝ => 1 ≤ x) (fun x => x ^ a * (log x + 1) ^ e) fun x => x ^ b :=
  ((dominated_log_add_one_pow_rpow (sub_pos.2 hab) e).mul_left
    fun x hx => rpow_nonneg (zero_le_one.trans hx) a).congr (fun _ _ => rfl) fun x hx => by
      rw [← rpow_add (zero_lt_one.trans_le hx), add_sub_cancel]

/-- Logarithms are absorbed: `x ^ a * (log x) ^ e = O(x ^ b)` on `x ≥ 1`, for `a < b`. -/
theorem dominated_rpow_mul_log_pow_rpow {a b : ℝ} (hab : a < b) (e : ℕ) :
    Dominated (fun x : ℝ => 1 ≤ x) (fun x => x ^ a * log x ^ e) fun x => x ^ b :=
  (dominated_rpow_mul_log_add_one_pow_rpow hab e).mono_left fun _ hx =>
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (log_nonneg hx) (le_add_of_nonneg_right zero_le_one) e)
      (rpow_nonneg (zero_le_one.trans hx) a)

/-! ### `log x + 1` and `⌈log_b n⌉ + 1` are `O(log)`, from `2` on -/





end ThreeSumApsp

end

end


-- Original source module: ThreeSumApsp.Sec4.Corollary26
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


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

/-- Proof of Corollary 26, "Setting up": "since the original D was larger than 4^{m-1}, the
assumption N ≥ D^18 now reads N ≥ 4^{18(m-1)}". -/
theorem Corollary26.hypothesis {D₀ N m : ℕ} (hgt : 4 ^ (m - 1) < D₀) (hN : D₀ ^ 18 ≤ N) :
    4 ^ (18 * (m - 1)) ≤ N := by
  rw [mul_comm, pow_mul]
  exact (Nat.pow_le_pow_left hgt.le 18).trans hN

/-! ### Boxes -/

/-- Proof of Corollary 26: "ρ = 9m/(L-m+1) = 9m/(20m+1) < 9/20, so 1/(1-ρ) < 2". -/
theorem Corollary26.rho_lt (m : ℕ) :
    rho (21 * m) m = 9 * (m : ℝ) / (20 * (m : ℝ) + 1) ∧ rho (21 * m) m < 9 / 20 ∧
      1 / (1 - rho (21 * m) m) < 2 := by
  have heq : rho (21 * m) m = 9 * (m : ℝ) / (20 * (m : ℝ) + 1) := by
    rw [rho]
    push_cast
    ring_nf
  have hlt : rho (21 * m) m < 9 / 20 := by
    rw [heq, div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  refine ⟨heq, hlt, ?_⟩
  rw [div_lt_iff₀ (by linarith)]
  linarith

/-- Proof of Corollary 26: "since t ≥ m/9, also ρ^t ≤ (9/20)^{m/9} = D^{-γ}". -/
theorem Corollary26.rho_pow_le (m : ℕ) :
    rho (21 * m) m ^ switchOf (1 / 9) m ≤ (9 / 20 : ℝ) ^ ((m : ℝ) / 9) ∧
      (9 / 20 : ℝ) ^ ((m : ℝ) / 9) = (D m : ℝ) ^ (-gammaOf 21 (1 / 9)) := by
  obtain ⟨-, hlt, -⟩ := Corollary26.rho_lt m
  constructor
  · calc rho (21 * m) m ^ switchOf (1 / 9) m
        ≤ (9 / 20 : ℝ) ^ switchOf (1 / 9) m :=
          pow_le_pow_left₀ (rho_nonneg (by omega)) hlt.le _
      _ = (9 / 20 : ℝ) ^ ((switchOf (1 / 9) m : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (9 / 20 : ℝ) ^ ((m : ℝ) / 9) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
            ((by ring_nf : (m : ℝ) / 9 = 1 / 9 * m).le.trans (Nat.le_ceil _))
  · -- `ρ_c = 9/20` at `c = 21`
    have h := rhoC_rpow_eq_D_rpow 21 (1 / 9) (by norm_num) m
    rwa [show rhoC 21 = 9 / 20 by norm_num [rhoC], show (1 / 9 : ℝ) * m = m / 9 by ring] at h

/-- Proof of Corollary 26: "γ := ln(20/9)/(9 ln 4)". This is the `γ` of Corollary 31 at `c = 21` and
`θ = 1/9`, where `ρ_c = 9/20`; the statements of this file write it `gammaOf 21 (1 / 9)`. -/
theorem Corollary26.gamma_eq : gammaOf 21 (1 / 9) = Real.log (20 / 9) / (9 * Real.log 4) := by
  have hfour : Real.log 4 ≠ 0 := log_four_pos.ne'
  rw [gammaOf, rhoC, show (1 / (9 / (21 - 1)) : ℝ) = 20 / 9 by norm_num]
  field_simp

/-- Proof of Corollary 26: "γ := ln(20/9)/(9 ln 4) = 0.0640…". The digits come from the bounds on
logarithms proved for Table 2. -/
theorem Corollary26.gamma_digits : 0.0640 < gammaOf 21 (1 / 9) ∧ gammaOf 21 (1 / 9) < 0.0641 := by
  have heq := gammaOf_eq_mul 21 (1 / 9)
  have hmem := gammaOf_21_one_mem
  exact ⟨by linarith [heq, hmem.1], by linarith [heq, hmem.2]⟩

/-- Proof of Corollary 26: "Hence the first term of (8) is O(m² N²/D^γ)". The common factor `N²` is
left out. -/
theorem Corollary26.first_term :
    Dominated (fun _ : ℕ => True)
      (fun m => ((21 * m : ℕ) : ℝ) * m *
        (rho (21 * m) m ^ switchOf (1 / 9) m / (1 - rho (21 * m) m)))
      fun m => (m : ℝ) ^ 2 * (D m : ℝ) ^ (-gammaOf 21 (1 / 9)) := by
  refine .of_le_const_mul (C := 42) (by norm_num) fun m _ => ?_
  obtain ⟨-, hlt, htwo⟩ := Corollary26.rho_lt m
  obtain ⟨hpow, heq⟩ := Corollary26.rho_pow_le m
  rw [heq] at hpow
  -- `ρ^t/(1-ρ) ≤ 2 D^{-γ}`
  have hdecay : rho (21 * m) m ^ switchOf (1 / 9) m / (1 - rho (21 * m) m)
      ≤ (D m : ℝ) ^ (-gammaOf 21 (1 / 9)) * 2 := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul hpow htwo.le (one_div_nonneg.2 (by linarith)) (by positivity)
  calc ((21 * m : ℕ) : ℝ) * m * (rho (21 * m) m ^ switchOf (1 / 9) m / (1 - rho (21 * m) m))
      ≤ ((21 * m : ℕ) : ℝ) * m * ((D m : ℝ) ^ (-gammaOf 21 (1 / 9)) * 2) := by
        gcongr
    _ = 42 * ((m : ℝ) ^ 2 * (D m : ℝ) ^ (-gammaOf 21 (1 / 9))) := by
        push_cast
        ring

/-! ### Queries -/

/-- `72^{m/9} (9/8)^m = D^q`: at `θ = 1/9` the number `x = (1-θ)/θ` is 8. -/
private lemma rpow_div_nine_eq (m : ℕ) :
    (72 : ℝ) ^ ((m : ℝ) / 9) * (9 / 8 : ℝ) ^ m = (D m : ℝ) ^ qOf (1 / 9) := by
  have h := rpow_mul_pow_eq_D_rpow_qOf (θ := 1 / 9) (by norm_num) (by norm_num) m
  rwa [show (9 * ((1 - 1 / 9) / (1 / 9)) : ℝ) = 72 by norm_num,
    show (1 + 1 / ((1 - 1 / 9) / (1 / 9)) : ℝ) = 9 / 8 by norm_num,
    show (1 / 9 : ℝ) * m = m / 9 by ring] at h

/-- Proof of Corollary 26, the display of the step "Queries": "∑_{d=0}^{t} binom(m, d) 9^d ≤ 72^t
∑_{d=0}^{m} binom(m, d) 8^{-d} = 72^t (9/8)^m < 72 · (72 · (9/8)^9)^{m/9} = 72 D^q", with
`t = ⌈m/9⌉`. -/
theorem Corollary26.sum_alpha_lt (m : ℕ) :
    ∑ d ∈ range (switchOf (1 / 9) m + 1), (alpha m d : ℝ) < 72 * (D m : ℝ) ^ qOf (1 / 9) := by
  set t : ℕ := switchOf (1 / 9) m
  have htm : t ≤ m := switchOf_le (by norm_num) m
  -- "t < m/9 + 1"
  have htlt : (t : ℝ) < (m : ℝ) / 9 + 1 := by
    have h : (t : ℝ) < 1 / 9 * (m : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  calc ∑ d ∈ range (t + 1), (alpha m d : ℝ)
      ≤ (9 * 8) ^ t * (1 + 1 / 8 : ℝ) ^ m := sum_alpha_le (by norm_num) (by norm_num) htm
    _ = 72 ^ t * (9 / 8 : ℝ) ^ m := by norm_num
    _ < 72 * (72 : ℝ) ^ ((m : ℝ) / 9) * (9 / 8 : ℝ) ^ m := by
        gcongr
        calc (72 : ℝ) ^ t = (72 : ℝ) ^ (t : ℝ) := (Real.rpow_natCast _ _).symm
          _ < (72 : ℝ) ^ ((m : ℝ) / 9 + 1) :=
              Real.rpow_lt_rpow_of_exponent_lt (by norm_num) htlt
          _ = 72 * (72 : ℝ) ^ ((m : ℝ) / 9) := by
              rw [Real.rpow_add (by norm_num), Real.rpow_one, mul_comm]
    _ = 72 * (D m : ℝ) ^ qOf (1 / 9) := by
        rw [mul_assoc, rpow_div_nine_eq]



/-- Proof of Corollary 26: "q := ln(72 · (9/8)^9)/(9 ln 4) = 0.4277…". The digits come from the
bounds on logarithms proved for Table 2. -/
theorem Corollary26.q_digits : 0.4277 < qOf (1 / 9) ∧ qOf (1 / 9) < 0.4278 :=
  ⟨lt_of_lt_of_le (by norm_num) qOf_ninth_mem.1, lt_of_le_of_lt qOf_ninth_mem.2 (by norm_num)⟩

/-- Proof of Corollary 26: "Hence a query takes O(L D^q) = O(m D^q) time." -/
theorem Corollary26.query_cost :
    Dominated (fun _ : ℕ => True) (fun m => costQuery (21 * m) m (switchOf (1 / 9) m))
      fun m => (m : ℝ) * (D m : ℝ) ^ qOf (1 / 9) := by
  refine .of_le_const_mul (C := 21 * 72) (by norm_num) fun m _ => ?_
  calc costQuery (21 * m) m (switchOf (1 / 9) m)
      ≤ ((21 * m : ℕ) : ℝ) * (72 * (D m : ℝ) ^ qOf (1 / 9)) :=
        mul_le_mul_of_nonneg_left (Corollary26.sum_alpha_lt m).le (Nat.cast_nonneg _)
    _ = 21 * 72 * ((m : ℝ) * (D m : ℝ) ^ qOf (1 / 9)) := by
        push_cast
        ring

/-! ### Encodings -/

/-- Proof of Corollary 26: "the standard bound [...] gives K = binom(21m, m) ≥ 1/(21m+1) ·
(21^21/20^20)^m". -/
theorem Corollary26.le_K {m : ℕ} (hm : 1 ≤ m) :
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



/-- Proof of Corollary 26: "the left-hand side of (10) is at most √(21m+1) · Λ^m". -/
theorem Corollary26.lhs10_le {m : ℕ} (hm : 1 ≤ m) :
    lhs10 (21 * m) m (gammaOf 21 (1 / 9)) ≤ Real.sqrt (21 * (m : ℝ) + 1) * baseLambda ^ m := by
  -- "D^γ = (20/9)^{m/9}, 10^L = 10^{21m}, and N₀ = 3^{20m}"
  have hD : (D m : ℝ) ^ gammaOf 21 (1 / 9) = ((20 / 9 : ℝ) ^ (1 / 9 : ℝ)) ^ m := by
    have hfour := log_four_pos.ne'
    rw [Corollary26.gamma_eq, cast_D_rpow, ← Real.rpow_mul_natCast (by norm_num),
      Real.rpow_def_of_pos (by norm_num)]
    congr 1
    field_simp
  have hN0 : (N0 (21 * m) m : ℝ) = ((3 : ℝ) ^ 20) ^ m := by
    rw [N0, show 21 * m - m = 20 * m by omega, pow_mul]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hroot : 0 < Real.sqrt (21 * (m : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hs : 0 < Real.sqrt (21 ^ 21 / 20 ^ 20) := Real.sqrt_pos.2 (by positivity)
  -- the bound on `K`, under the square root
  have hK : Real.sqrt (21 ^ 21 / 20 ^ 20) ^ m / Real.sqrt (21 * (m : ℝ) + 1)
      ≤ Real.sqrt (K (21 * m) m) := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [div_pow, ← pow_mul, mul_comm m 2, pow_mul, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    exact Corollary26.le_K hm
  rw [lhs10, sqrtKN0, hD, hN0, pow_mul]
  calc ((20 / 9 : ℝ) ^ (1 / 9 : ℝ)) ^ m * ((10 : ℝ) ^ 21) ^ m
        / (Real.sqrt (K (21 * m) m) * ((3 : ℝ) ^ 20) ^ m)
      ≤ ((20 / 9 : ℝ) ^ (1 / 9 : ℝ)) ^ m * ((10 : ℝ) ^ 21) ^ m
        / (Real.sqrt (21 ^ 21 / 20 ^ 20) ^ m / Real.sqrt (21 * (m : ℝ) + 1)
          * ((3 : ℝ) ^ 20) ^ m) := by
        gcongr
    _ = Real.sqrt (21 * (m : ℝ) + 1) * baseLambda ^ m := by
        rw [baseLambda, div_pow, mul_pow, mul_pow]
        field_simp

/-- Proof of Corollary 26: `Λ` "= 4.198… · 10^10". Eighteenth powers are compared: `Λ^18` is a
rational number. -/
theorem baseLambda_numeric : 4.198 * 10 ^ 10 < baseLambda ∧ baseLambda < 4.199 * 10 ^ 10 := by
  have hpow : baseLambda ^ 18
      = (10 ^ 21) ^ 18 * (20 / 9) ^ 2 / ((21 ^ 21 / 20 ^ 20) ^ 9 * (3 ^ 20) ^ 18) := by
    rw [baseLambda, div_pow, mul_pow, mul_pow, ← Real.rpow_mul_natCast (by norm_num),
      pow_mul (Real.sqrt _) 2 9, Real.sq_sqrt (by positivity)]
    norm_num
  exact ⟨lt_of_pow_lt_pow_left₀ 18 (by unfold baseLambda; positivity) (by rw [hpow]; norm_num),
    lt_of_pow_lt_pow_left₀ 18 (by norm_num) (by rw [hpow]; norm_num)⟩

/-- Proof of Corollary 26: "Its base 4^18 = 6.871… · 10^10". -/
theorem four_pow_eighteen_numeric :
    6.871 * 10 ^ 10 < (4 : ℝ) ^ 18 ∧ (4 : ℝ) ^ 18 < 6.872 * 10 ^ 10 := by
  constructor <;> norm_num

/-- Proof of Corollary 26: `4^18` "is larger than Λ by a factor of more than 1.63". -/
theorem baseLambda_mul_lt : 1.63 * baseLambda < 4 ^ 18 :=
  calc 1.63 * baseLambda < 1.63 * (4.199 * 10 ^ 10) :=
        mul_lt_mul_of_pos_left baseLambda_numeric.2 (by norm_num)
    _ < 6.871 * 10 ^ 10 := by norm_num
    _ < 4 ^ 18 := four_pow_eighteen_numeric.1

/-- Proof of Corollary 26: "1.63^m ≥ 4^18 √(21m+1), which is the case for all m ≥ 60". -/
theorem Corollary26.threshold {m : ℕ} (hm : 60 ≤ m) :
    (4 : ℝ) ^ 18 * Real.sqrt (21 * (m : ℝ) + 1) ≤ 1.63 ^ m := by
  -- the squares: `4^36 (21m + 1) ≤ 1.63^{2m}`, by induction from `m = 60`
  have hsq : (4 : ℝ) ^ 36 * (21 * (m : ℝ) + 1) ≤ (1.63 ^ m) ^ 2 := by
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      have hn' : (60 : ℝ) ≤ n := by exact_mod_cast hn
      rw [pow_succ (1.63 : ℝ), mul_pow]
      push_cast
      -- `1.63²` times the bound for `n`, and `21 (n + 1) + 1 ≤ 1.63² (21n + 1)`
      linarith [ih, hn']
  rw [← le_div_iff₀' (by positivity)]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rwa [div_pow, le_div_iff₀' (by positivity), ← pow_mul]

/-- Equation (10), `D^γ · 10^L / (√K N₀) ≤ N`, where it is printed, in the proof of Corollary 26.
There `D = 4^m`, "L := 21m", "γ := ln(20/9)/(9 ln 4)", "K = binom(21m, m)", "N₀ = 3^{20m}", and "the
assumption N ≥ D^18 now reads N ≥ 4^{18(m-1)}". The inequality "holds whenever
1.63^m ≥ 4^18 √(21m+1), which is the case for all m ≥ 60". -/
theorem eq_10_corollary_26 (m N : ℕ) (hm : 60 ≤ m) (hN : 4 ^ (18 * (m - 1)) ≤ N) :
    (D m : ℝ) ^ (Real.log (20 / 9) / (9 * Real.log 4)) * (10 : ℝ) ^ (21 * m)
        / (Real.sqrt (K (21 * m) m) * (N0 (21 * m) m : ℝ))
      ≤ (N : ℝ) := by
  have hΛ0 : 0 ≤ baseLambda := by linarith [baseLambda_numeric.1]
  have hΛ : baseLambda ≤ 4 ^ 18 / 1.63 := by
    rw [le_div_iff₀' (by norm_num)]
    exact baseLambda_mul_lt.le
  rw [← Corollary26.gamma_eq]
  calc lhs10 (21 * m) m (gammaOf 21 (1 / 9))
      ≤ Real.sqrt (21 * (m : ℝ) + 1) * baseLambda ^ m := Corollary26.lhs10_le (by omega)
    _ ≤ Real.sqrt (21 * (m : ℝ) + 1) * ((4 : ℝ) ^ 18 / 1.63) ^ m := by gcongr
    _ = (4 : ℝ) ^ 18 * Real.sqrt (21 * (m : ℝ) + 1) / 1.63 ^ m * (4 : ℝ) ^ (18 * (m - 1)) := by
        obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
        rw [Nat.add_sub_cancel, div_pow, ← pow_mul]
        field_simp
        ring
    _ ≤ 1 * (4 : ℝ) ^ (18 * (m - 1)) := by
        gcongr
        exact (div_le_one (by positivity)).2 (Corollary26.threshold hm)
    _ ≤ (N : ℝ) := by
        rw [one_mul]
        exact_mod_cast hN

/-! ### Conclusion -/



/-- Inequality (10) holds in this range (`eq_10_corollary_26`). -/
theorem Sizes.Large26.lhs10_le {p : Sizes} (h : p.Large26) :
    lhs10 (21 * p.m) p.m (gammaOf 21 (1 / 9)) ≤ p.N := by
  rw [Corollary26.gamma_eq]
  exact eq_10_corollary_26 p.m p.N h.m_ge h.N_ge

/-- Proof of Corollary 26, "Conclusion": "For m ≥ 60, Theorem 30 thus applies": its hypothesis
`N ≥ √K N₀` holds. -/
theorem Corollary26.tile_fits {p : Sizes} (h : p.Large26) : sqrtKN0 (21 * p.m) p.m ≤ p.N :=
  Equation10.tile_fits (by omega) (by linarith [Corollary26.gamma_digits.1]) h.lhs10_le

/-- Proof of Corollary 26, "Conclusion": "The preprocessing takes O(m² N²/D^γ) time and space". -/
theorem Corollary26.preprocessing :
    Dominated Sizes.Large26 (fun p => cost8 (21 * p.m) p.m (switchOf (1 / 9) p.m) p.N)
      fun p => (p.m : ℝ) ^ 2 * (D p.m : ℝ) ^ (-gammaOf 21 (1 / 9)) * (p.N : ℝ) ^ 2 :=
  dominated_cost8_of_eq_10 (Lof := fun m => 21 * m) Corollary26.first_term (fun _ _ => trivial)
    (fun p hp => le_mul_of_one_le_left (by positivity)
      (one_le_pow₀ (Nat.one_le_cast.2 (le_trans (by norm_num) hp.m_ge))))
    fun _ hp => hp.lhs10_le

/-- Proof of Corollary 26, "Conclusion": "Since m = O(log D) and the exponents γ - 0.063 and 0.437 -
q are positive, we have m² = O(D^{γ-0.063}) and m = O(D^{0.437-q})". In general, `m^e D^a = O(D^b)`
for `D = 4^m` and `a < b`. -/
theorem dominated_pow_mul_D_rpow {a b : ℝ} (hab : a < b) (e : ℕ) :
    Dominated (fun _ : ℕ => True) (fun m => (m : ℝ) ^ e * (D m : ℝ) ^ a)
      fun m => (D m : ℝ) ^ b := by
  refine ((dominated_rpow_mul_log_pow_rpow hab e).comp (fun m : ℕ => (D m : ℝ))
    fun m (_ : True) => one_le_cast_D m).mono_left fun m _ => ?_
  have hm := cast_le_log_cast_D m
  rw [mul_comm]
  gcongr

/-- Proof of Corollary 26, "Conclusion", with `D = 4^m`: "which gives the bounds O(N²/D^{0.063}) and
O(D^{0.437}) of the corollary". -/
theorem Corollary26.conclusion :
    Dominated Sizes.Large26 (fun p => cost8 (21 * p.m) p.m (switchOf (1 / 9) p.m) p.N)
        (fun p => (D p.m : ℝ) ^ (-0.063 : ℝ) * (p.N : ℝ) ^ 2) ∧
      Dominated (fun _ : ℕ => True) (fun m => costQuery (21 * m) m (switchOf (1 / 9) m))
        fun m => (D m : ℝ) ^ (0.437 : ℝ) := by
  -- "the exponents γ - 0.063 and 0.437 - q are positive"
  have hγ : -gammaOf 21 (1 / 9) < -0.063 := by linarith [Corollary26.gamma_digits.1]
  have hq : qOf (1 / 9) < 0.437 := by linarith [Corollary26.q_digits.2]
  exact ⟨Corollary26.preprocessing.trans
      (((dominated_pow_mul_D_rpow hγ 2).comp Sizes.m fun _ _ => trivial).mul_right
        fun _ _ => sq_nonneg _),
    Corollary26.query_cost.trans (by simpa only [pow_one] using dominated_pow_mul_D_rpow hq 1)⟩



/-- `D ≥ 2`, since `m = 0` for `D ≤ 1`. -/
theorem Sizes.Corollary26.setUp {p : Sizes} (h : p.Corollary26) : p.SetUp := by
  obtain ⟨-, hm, hm60⟩ := h
  refine ⟨?_, hm⟩
  by_contra hlt
  obtain h0 | h1 : p.D₀ = 0 ∨ p.D₀ = 1 := by omega
  · simp only [h0, Nat.cast_zero, Real.logb_zero, Nat.ceil_zero] at hm
    omega
  · simp only [h1, Nat.cast_one, Real.logb_one, Nat.ceil_zero] at hm
    omega

/-- After "Setting up", these instances are in the range of the step "Conclusion". -/
theorem Sizes.Corollary26.large {p : Sizes} (h : p.Corollary26) : p.Large26 :=
  ⟨h.m_ge, Corollary26.hypothesis h.setUp.gt h.N_ge⟩

/-- Corollary 26, the costs of Theorem 30 at "L := 21m and t := ⌈m/9⌉", in terms of the given `D`:
there is a constant `C` such that for all `N ≥ D^{18}` with `m = ⌈log_4 D⌉ ≥ 60` the hypothesis
`N ≥ √K N₀` of Theorem 30 holds, the expression (8) is at most `C N²/D^{0.063}`, and the query cost
is at most `C D^{0.437}`. -/
theorem Corollary26.costs :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D₀ N m : ℕ, D₀ ^ 18 ≤ N → m = ⌈Real.logb 4 (D₀ : ℝ)⌉₊ → 60 ≤ m →
      sqrtKN0 (21 * m) m ≤ N ∧
      cost8 (21 * m) m (switchOf (1 / 9) m) N ≤ C * ((N : ℝ) ^ 2 / (D₀ : ℝ) ^ (0.063 : ℝ)) ∧
      costQuery (21 * m) m (switchOf (1 / 9) m) ≤ C * (D₀ : ℝ) ^ (0.437 : ℝ) := by
  -- the padding "changes D by a factor less than 4, which only affects the constants"
  have hpad : ∀ a : ℝ, Dominated Sizes.Corollary26 (fun p => (D p.m : ℝ) ^ a)
      fun p => (p.D₀ : ℝ) ^ a := fun a => by
    simpa only [pow_zero, mul_one] using (padded_le a 0).mono_dom fun _ hp => hp.setUp
  have hpre := ((Corollary26.conclusion.1.mono_dom fun _ hp => hp.large).trans
    ((hpad (-0.063)).mul_right fun _ _ => sq_nonneg _)).congr (fun _ _ => rfl)
      fun p _ => show (p.D₀ : ℝ) ^ (-0.063 : ℝ) * (p.N : ℝ) ^ 2
          = (p.N : ℝ) ^ 2 / (p.D₀ : ℝ) ^ (0.063 : ℝ) by
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        ring
  have hquery := (Corollary26.conclusion.2.comp Sizes.m fun _ _ => trivial).trans (hpad 0.437)
  obtain ⟨C, hC, hboth⟩ := hpre.exists_const_and hquery (fun _ _ => by positivity)
    fun _ _ => by positivity
  exact ⟨C, hC, fun D₀ N m hN hm hm60 =>
    have hp : Sizes.Corollary26 ⟨D₀, N, m⟩ := ⟨hN, hm, hm60⟩
    ⟨Corollary26.tile_fits hp.large, hboth _ hp⟩⟩



/-! ### The parameters `c = 21` and `θ = 1/9` of Corollary 31 and Table 2

The sentence before Corollary 26 says: "It is the entry c = 21, q = 0.43 of Table 2". The parameters
of the proof above are those of Corollary 31 at `c = 21`, `θ = 1/9`: this holds for `L`
(`levelsOf_21`), for `γ` and `q` (`Corollary26.gamma_eq` and `Corollary26.q_eq` above), and for `Λ`
(`baseLambda_eq_exp_lnΛ`). The condition `ε < R_c(γ)` holds at `ε = 1/18` (`Corollary26.Rc_digits`),
and `N ≥ D^18` gives the condition `D ≤ N^{0.056}` of the row `c = 21` of the table, which is
`table_2_c21` (`Corollary26.row_condition`). Nothing else rests on this section. -/









end ThreeSumApsp

end

end


-- Original source module: ThreeSumApsp.Util.Ceil
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Ceilings of quotients and logarithms, floors and ceilings of roots

General facts about natural and real numbers. The quotient of two natural numbers, rounded up, is
Mathlib's `a ⌈/⌉ b`. It is computed by `Nat.ceilDiv_eq_add_pred_div : a ⌈/⌉ b = (a + b - 1) / b`.
It is the ceiling of the real quotient (`Nat.ceil_div_eq_ceilDiv`) and the least `k` with
`a ≤ k * b` (`Nat.ceilDiv_le_iff`, `Nat.lt_ceilDiv_iff`), so `a ≤ a ⌈/⌉ b * b < a + b`
(`Nat.le_ceilDiv_mul`, `Nat.ceilDiv_mul_lt`). The power of `b` with exponent `⌈log_b n⌉` is at most
`b * n` (`Nat.pow_clog_le_mul`). A natural number is compared with an `e`-th root by its `e`-th
power (`Real.natCast_le_rpow_inv_iff`, `Real.rpow_inv_le_natCast_iff`). `cbrtCeil n` is the cube
root of `n`, rounded up.
-/

public section

namespace Nat

/-! ## The ceiling of a quotient of natural numbers -/

/-- `a ⌈/⌉ b ≤ k` says that `k` pieces of size `b` cover `a`. Mathlib's `ceilDiv_le_iff_le_mul` has
`b * k` on the right. -/
theorem ceilDiv_le_iff {a b k : ℕ} (hb : 0 < b) : a ⌈/⌉ b ≤ k ↔ a ≤ k * b := by
  rw [ceilDiv_le_iff_le_mul hb, Nat.mul_comm]









/-- The ceiling of the real quotient of two natural numbers, in natural numbers. -/
theorem ceil_div_eq_ceilDiv (a : ℕ) {b : ℕ} (hb : 0 < b) : ⌈(a : ℝ) / (b : ℝ)⌉₊ = a ⌈/⌉ b := by
  refine eq_of_forall_ge_iff fun k => ?_
  rw [Nat.ceil_le, div_le_iff₀ (Nat.cast_pos.2 hb), ceilDiv_le_iff hb]
  exact_mod_cast Iff.rfl

/-! ## The ceiling of a logarithm

`Real.natCeil_logb_natCast : ⌈Real.logb b n⌉₊ = Nat.clog b n` passes from real to natural numbers,
and `Nat.le_pow_clog : 1 < b → x ≤ b ^ Nat.clog b x` is the lower bound. -/



end Nat

namespace Real

/-! ## Roots

The `e`-th root of `t` is written `(t : ℝ) ^ ((e : ℝ)⁻¹)`. With these two lemmas,
`Nat.le_floor_iff` and `Nat.ceil_le`, its floor and its ceiling are described by powers of natural
numbers. -/





end Real

namespace ThreeSumApsp



end ThreeSumApsp

end

end


-- Original source module: ThreeSumApsp.Sec4.Corollary31.RationalParameters
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Rational parameters for Corollary 31

Corollary 31 has real parameters `c > 10` and `0 < θ < 0.9`, and a real `ε < R_c(γ)` with
`γ = θ ln(1/ρ_c)/ln 4`. A program can only contain rational numbers. This file shows that the
parameters can be replaced by rational ones without loss (`exists_rat_params`): first a rational
`c' > c` so close to `c` that `ε` is still below `R_{c'}(γ)`, by continuity (`continuousAt_Rc`);
then a rational `θ' < θ` so close to `θ` that the exponent `γ` of `c'` and `θ'` is still at least
that of `c` and `θ`. A smaller `θ` makes `q` smaller and `R_{c'}(γ)` larger. The file also writes
the numbers `⌈c m⌉` and `⌈θ m⌉` for rational parameters in integer arithmetic (`levelsOf_div`,
`switchOf_div`).
-/

@[expose] public section

namespace ThreeSumApsp













/-- `t = ⌈θ m⌉` for a rational `θ = p/q`. -/
theorem switchOf_div (p m : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    switchOf ((p : ℝ) / q) m = (p * m + q - 1) / q := by
  unfold switchOf
  rw [← Nat.ceilDiv_eq_add_pred_div, ← Nat.ceil_div_eq_ceilDiv (p * m) hq]
  congr 1
  push_cast
  ring

end ThreeSumApsp

end

end


-- Original source module: ThreeSumApsp.Programs.Sec4.Corollary26.Regime
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Corollary 26: the parameters 21, 1/9 and 60, and the regime N ≥ D^18

Corollary 26 is the case c = 21, θ = 1/9 of the programs with rational parameters, with the
threshold 60 (`ratParams26`): the preprocessing calls that of Theorem 30 with L = 21 m and t = ⌈m/9⌉
if m = ⌈log₄ D⌉ ≥ 60. On the inputs with N ≥ D^18, and for m ≥ 60, the hypotheses of Theorem 30 hold
at these L and t (`hyp30_26`), and its two cost expressions are O(N²/D^{0.063}) and O(D^{0.437})
(`costs26`); both come from `Corollary26.costs`. Then the bound N²/D^{0.063} (`preBound26`) and what
is used about it. `regime26` puts this in the form in which the statements about the programs with
rational parameters ask for it (`CostsWithin`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec Finset

/-! ## The parameters -/



/-- L = 21 m. -/
theorem ratParams26_L (m : ℕ) : ratParams26.L m = 21 * m := by
  simp [RatParams.L, ratParams26]

/-- t = ⌈m/9⌉. -/
theorem ratParams26_t (m : ℕ) : ratParams26.t m = (m + 8) / 9 := by
  simp [RatParams.t, ratParams26]






/-- At the parameters of Corollary 26, Theorem 30 is used with L = 21 m. -/
theorem parOf_ratParams26 (N D₀ : ℕ) : parOf ratParams26 N D₀ = par26 N D₀ := by
  simp only [parOf, par26, ratParams26_L]

/-- At the parameters of Corollary 26, Theorem 30 is used with t = ⌈m/9⌉. -/
theorem switchOf31_ratParams26 (D₀ : ℕ) : switchOf31 ratParams26 D₀ = switch26 D₀ := by
  simp only [switchOf31, switch26, ratParams26_t]

/-- The ceiling ⌈m/9⌉ in natural numbers. -/
theorem switchOf_ninth (m : ℕ) : switchOf (1 / 9) m = (m + 8) / 9 := by
  have h := switchOf_div 1 m (q := 9) (by norm_num)
  norm_num at h
  exact h

/-! ## The two cost expressions -/



/-- **The costs of Theorem 30 at the parameters of Corollary 26**, for m ≥ 60. -/
theorem costs26 : ∃ C : ℝ, 0 ≤ C ∧
    ∀ D₀ N : ℕ, D₀ ^ 18 ≤ N → 60 ≤ logFour D₀ → Hyp30 (par26 N D₀) (switch26 D₀) ∧
      cost8 (21 * logFour D₀) (logFour D₀) (switch26 D₀) N ≤ C * preBound26 D₀ N ∧
      costQuery (21 * logFour D₀) (logFour D₀) (switch26 D₀) ≤ C * (D₀ : ℝ) ^ (0.437 : ℝ) := by
  obtain ⟨C, hC, h⟩ := Corollary26.costs
  refine ⟨C, hC, fun D₀ N hN hm => ?_⟩
  obtain ⟨hN0, hcost8, hquery⟩ := h D₀ N (logFour D₀) hN (ceil_logb_four D₀).symm hm
  rw [switchOf_ninth] at hcost8 hquery
  refine ⟨⟨le_trans (by norm_num) hm, ?_, ?_, hN0⟩, hcost8, hquery⟩
  · change 10 * logFour D₀ ≤ 21 * logFour D₀
    omega
  · change (logFour D₀ + 8) / 9 ≤ logFour D₀
    omega

/-- Proof of Corollary 26: "For m ≥ 60, Theorem 30 thus applies". -/
theorem hyp30_26 {N D₀ : ℕ} (hN : D₀ ^ 18 ≤ N) (hm : 60 ≤ logFour D₀) :
    Hyp30 (par26 N D₀) (switch26 D₀) := by
  obtain ⟨_, -, hcosts⟩ := costs26
  exact (hcosts D₀ N hN hm).1

/-! ## The overheads -/



/-- N ≥ 1, because N ≥ D^18. -/
theorem one_le_of_pow_eighteen_le {D₀ N : ℕ} (hD : 1 ≤ D₀) (hN : D₀ ^ 18 ≤ N) : 1 ≤ N :=
    le_trans (Nat.one_le_pow _ _ hD) hN

/-- N ≥ D, because N ≥ D^18. -/
theorem le_of_pow_eighteen_le {D₀ N : ℕ} (hD : 1 ≤ D₀) (hN : D₀ ^ 18 ≤ N) : D₀ ≤ N := by
  refine le_trans ?_ hN
  calc D₀ = D₀ ^ 1 := (pow_one _).symm
    _ ≤ D₀ ^ 18 := Nat.pow_le_pow_right hD (by norm_num)



/-! ## The regime -/



end Light.Sec4

end

end


-- Original source module: Research.InnerBound
section


set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace Research

open ThreeSumApsp ThreeSumApsp.Spec Light Light.Sec4

/-- The unchanged Corollary 26 data structure supports the stronger exponents .064 and .436. -/
theorem conclusion_064 :
    Dominated Sizes.Large26 (fun p => cost8 (21 * p.m) p.m (switchOf (1 / 9) p.m) p.N)
        (fun p => (D p.m : ℝ) ^ (-0.064 : ℝ) * (p.N : ℝ) ^ 2) ∧
      Dominated (fun _ : ℕ => True) (fun m => costQuery (21 * m) m (switchOf (1 / 9) m))
        fun m => (D m : ℝ) ^ (0.436 : ℝ) := by
  have hγ : -gammaOf 21 (1 / 9) < -0.064 := by linarith [Corollary26.gamma_digits.1]
  have hq : qOf (1 / 9) < 0.436 := by linarith [Corollary26.q_digits.2]
  exact ⟨Corollary26.preprocessing.trans
      (((dominated_pow_mul_D_rpow hγ 2).comp Sizes.m fun _ _ => trivial).mul_right
        fun _ _ => sq_nonneg _),
    Corollary26.query_cost.trans (by simpa only [pow_one] using dominated_pow_mul_D_rpow hq 1)⟩

theorem costs_064 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D₀ N m : ℕ, D₀ ^ 18 ≤ N → m = ⌈Real.logb 4 (D₀ : ℝ)⌉₊ → 60 ≤ m →
      sqrtKN0 (21 * m) m ≤ N ∧
      cost8 (21 * m) m (switchOf (1 / 9) m) N ≤ C * ((N : ℝ) ^ 2 / (D₀ : ℝ) ^ (0.064 : ℝ)) ∧
      costQuery (21 * m) m (switchOf (1 / 9) m) ≤ C * (D₀ : ℝ) ^ (0.436 : ℝ) := by
  have hpad : ∀ a : ℝ, Dominated Sizes.Corollary26 (fun p => (D p.m : ℝ) ^ a)
      fun p => (p.D₀ : ℝ) ^ a := fun a => by
    simpa only [pow_zero, mul_one] using (padded_le a 0).mono_dom fun _ hp => hp.setUp
  have hpre := ((conclusion_064.1.mono_dom fun _ hp => hp.large).trans
    ((hpad (-0.064)).mul_right fun _ _ => sq_nonneg _)).congr (fun _ _ => rfl)
      fun p _ => show (p.D₀ : ℝ) ^ (-0.064 : ℝ) * (p.N : ℝ) ^ 2
          = (p.N : ℝ) ^ 2 / (p.D₀ : ℝ) ^ (0.064 : ℝ) by
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        ring
  have hquery := (conclusion_064.2.comp Sizes.m fun _ _ => trivial).trans (hpad 0.436)
  obtain ⟨C, hC, hboth⟩ := hpre.exists_const_and hquery (fun _ _ => by positivity)
    fun _ _ => by positivity
  exact ⟨C, hC, fun D₀ N m hN hm hm60 =>
    have hp : Sizes.Corollary26 ⟨D₀, N, m⟩ := ⟨hN, hm, hm60⟩
    ⟨Corollary26.tile_fits hp.large, hboth _ hp⟩⟩

noncomputable def preBound064 (N D₀ : ℕ) : ℝ := (N : ℝ) ^ 2 / (D₀ : ℝ) ^ (0.064 : ℝ)

theorem regime_064 : ∃ C : ℝ, 0 ≤ C ∧ ∀ N D₀ : ℕ, 1 ≤ D₀ → D₀ ^ 18 ≤ N →
    CostsWithin ratParams26 C N D₀ (preBound064 N D₀) ((D₀ : ℝ) ^ (0.436 : ℝ)) := by
  obtain ⟨C, hC, hcost⟩ := costs_064
  refine ⟨C, hC, fun N D₀ hD hN => ⟨one_le_of_pow_eighteen_le hD hN, hD,
    le_of_pow_eighteen_le hD hN, one_le_sq_div_rpow hD hN (by norm_num),
    Real.one_le_rpow (by exact_mod_cast hD) (by norm_num), fun hm => ?_⟩⟩
  rw [parOf_ratParams26, switchOf31_ratParams26, ratParams26_L]
  obtain ⟨hfit, hpre, hquery⟩ := hcost D₀ N (logFour D₀) hN (ceil_logb_four D₀).symm hm
  rw [switchOf_ninth] at hpre hquery
  exact ⟨hyp30_26 hN hm, hpre, hquery⟩

theorem allInstancesTime26_le_064 (c : ℕ) : ∃ C : ℝ, ∀ N D₀ w U : ℕ,
    1 ≤ D₀ → D₀ ^ 18 ≤ N →
    (allInstancesTime26 c [N, D₀, w, U] : ℝ)
      ≤ C * ((w : ℝ) * (D₀ : ℝ) ^ (0.436 : ℝ) + preBound064 N D₀) := by
  obtain ⟨C, hC, hreg⟩ := regime_064
  obtain ⟨A, hA⟩ := exists_tOffline32_le ratParams26 hC c 400
  refine ⟨A, fun N D₀ w U hD hN => ?_⟩
  have htime : (allInstancesTime26 c [N, D₀, w, U] : ℝ)
      = (tOffline32 c ratParams26 N D₀ w : ℝ) + (400 : ℕ) := by
    simp only [allInstancesTime26, if_pos hN]
    push_cast
    ring
  rw [htime]
  refine (hA w (hreg N D₀ hD hN)).trans (le_of_eq ?_)
  ring

private theorem allInstancesTime26_mono (c N D₀ : ℕ) {w w' : ℕ}
    (U U' : ℕ) (hw : w ≤ w') :
    allInstancesTime26 c [N, D₀, w, U] ≤ allInstancesTime26 c [N, D₀, w', U'] := by
  change 400 + (if D₀ ^ 18 ≤ N then tOffline32 c ratParams26 N D₀ w else 40 * ((w + 1) * (D₀ + 1)))
    ≤ 400 + (if D₀ ^ 18 ≤ N then tOffline32 c ratParams26 N D₀ w' else 40 * ((w' + 1) * (D₀ + 1)))
  split_ifs
  · unfold tOffline32
    have := Nat.mul_le_mul_right (tQuery31 ratParams26 D₀ + 30) hw
    omega
  · have := Nat.mul_le_mul_right (D₀ + 1) (show w + 1 ≤ w' + 1 by omega)
    omega

noncomputable def thinTime064 (N D₀ w : ℕ) (_u : ℝ) : ℝ :=
  (allInstancesTime26 cShared30 [N, D₀, w, 0] : ℝ)

theorem thin_solved_064 : lightModel.thinProduct thinTime064 := by
  refine ⟨_, _, _, _, allInstancesNeed26_poly, allInstances26_program26,
    fun N D₀ w w' U u _ _ _ hw _ => ?_⟩
  change (allInstancesTime26 cShared30 [N, D₀, w, U] : ℝ) ≤
      (allInstancesTime26 cShared30 [N, D₀, w', 0] : ℝ)
  exact_mod_cast allInstancesTime26_mono cShared30 N D₀ U 0 hw

theorem wanted_064_le (N D₀ w : ℕ) (hD : 1 ≤ D₀)
    (hw : (w : ℝ) ≤ (N : ℝ) ^ 2 / Real.sqrt D₀) :
    (w : ℝ) * (D₀ : ℝ) ^ (0.436 : ℝ) + preBound064 N D₀ ≤ 2 * preBound064 N D₀ := by
  have hD0 : (0 : ℝ) < D₀ := by exact_mod_cast hD
  have hprod : (D₀ : ℝ) ^ (0.436 : ℝ) * (D₀ : ℝ) ^ (0.064 : ℝ) = Real.sqrt D₀ := by
    rw [← Real.rpow_add hD0, Real.sqrt_eq_rpow]
    norm_num
  have hp : 0 < (D₀ : ℝ) ^ (0.064 : ℝ) := Real.rpow_pos_of_pos hD0 _
  have hq : 0 < (D₀ : ℝ) ^ (0.436 : ℝ) := Real.rpow_pos_of_pos hD0 _
  have hs : 0 < Real.sqrt (D₀ : ℝ) := Real.sqrt_pos.2 hD0
  have hqueries : (w : ℝ) * (D₀ : ℝ) ^ (0.436 : ℝ) ≤ preBound064 N D₀ := by
    calc (w : ℝ) * (D₀ : ℝ) ^ (0.436 : ℝ)
        ≤ ((N : ℝ) ^ 2 / Real.sqrt D₀) * (D₀ : ℝ) ^ (0.436 : ℝ) := by gcongr
      _ = preBound064 N D₀ := by
        rw [preBound064, ← hprod]
        field_simp
  linarith

/-- The existing inner program, with a sharpened analysis, saves D^.064 per reduction instance. -/
theorem lopDetect_064Proof : ∃ (C : ℝ) (T : ℕ → ℕ → ℕ → ℝ), 0 ≤ C ∧
    lightModel.lopDetect T ∧ ∀ n D₀ : ℕ, 1 ≤ D₀ → D₀ ^ 18 ≤ n →
      T n D₀ (queryCap n D₀) ≤ C * ((n : ℝ) ^ 2 / (D₀ : ℝ) ^ (0.064 : ℝ)) := by
  obtain ⟨C₁, hcount⟩ := Light.Sec3.claim_lopCountFromThinProduct
  obtain ⟨C₃, hdetect⟩ := Light.Sec3.claim_lopDetectFromCount
  obtain ⟨A, hA⟩ := allInstancesTime26_le_064 cShared30
  let dom : ℕ × ℕ → Prop := fun p => 1 ≤ p.2 ∧ p.2 ^ 18 ≤ p.1
  let bound : ℕ × ℕ → ℝ := fun p => preBound064 p.1 p.2
  have hcap (n D₀ : ℕ) : (queryCap n D₀ : ℝ) ≤ (n : ℝ) ^ 2 / Real.sqrt D₀ :=
    Nat.floor_le (by positivity)
  have ht : Dominated dom (fun p => thinTime064 p.1 p.2 (queryCap p.1 p.2) 1) bound := by
    refine Dominated.of_exists_const ⟨2 * A, ?_⟩ (fun _ _ => by dsimp [bound, preBound064]; positivity)
    intro p hp
    have h := hA p.1 p.2 (queryCap p.1 p.2) 0 hp.1 hp.2
    have hAnn : 0 ≤ A := by
      have hbase := hA 1 1 0 0 (by norm_num) (by norm_num)
      norm_num [preBound064] at hbase
      exact le_trans (Nat.cast_nonneg _) hbase
    calc thinTime064 p.1 p.2 (queryCap p.1 p.2) 1
        ≤ A * ((queryCap p.1 p.2 : ℝ) * (p.2 : ℝ) ^ (0.436 : ℝ) + preBound064 p.1 p.2) := h
      _ ≤ A * (2 * preBound064 p.1 p.2) :=
        mul_le_mul_of_nonneg_left (wanted_064_le _ _ _ hp.1 (hcap _ _)) hAnn
      _ = (2 * A) * bound p := by dsimp [bound]; ring
  have hnD : Dominated dom (fun p => (p.1 : ℝ) * p.2) bound :=
    .of_le fun p hp => mul_le_sq_div_rpow hp.1 hp.2 (by norm_num)
  have hw : Dominated dom (fun p => (queryCap p.1 p.2 : ℝ)) bound :=
    .of_le fun p hp => (hcap _ _).trans (sq_div_sqrt_le_sq_div_rpow p.1 hp.1 (by norm_num))
  have hone : Dominated dom (fun _ => (1 : ℝ)) bound :=
    .of_le fun p hp => one_le_sq_div_rpow hp.1 hp.2 (by norm_num)
  obtain ⟨C, hC, hbound⟩ :=
    (ht.add (((hnD.add hw).add hone).const_mul_of_nonneg C₁ fun p _ => by positivity)).add
      ((hw.add hone).const_mul_of_nonneg C₃ fun p _ => by positivity)
  exact ⟨C, _, hC, hdetect _ (hcount _ thin_solved_064), fun n D₀ hD hN => hbound (n, D₀) ⟨hD, hN⟩⟩

end Research

end

end


open ThreeSumApsp in
theorem solution : ∃ (C : ℝ) (T : ℕ → ℕ → ℕ → ℝ), 0 ≤ C ∧
    Light.lightModel.lopDetect T ∧ ∀ n D₀ : ℕ, 1 ≤ D₀ → D₀ ^ 18 ≤ n →
      T n D₀ (queryCap n D₀) ≤ C * ((n : ℝ) ^ 2 / (D₀ : ℝ) ^ (0.064 : ℝ)) :=
  Research.lopDetect_064Proof

#print axioms solution
