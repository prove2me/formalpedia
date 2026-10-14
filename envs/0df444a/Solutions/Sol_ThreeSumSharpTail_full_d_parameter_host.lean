-- Prove2me | solution 1 for ThreeSumSharpTail.full_d_parameter_host
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T19:14:48.610195+00:00
-- url     : https://prove2.me/submissions/b465eeec-7c94-467e-9cdc-21f9e339cb6d

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
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Hashing
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Statements_Exponents
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Corollary15_16
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Scale
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Digits
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
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
import Definitions.Def_APSP299791_Defs3
import Definitions.Def_APSP299791_Defs4
import Theorems.Thm_Light_Sec3_et17_spec
import Theorems.Thm_Light_Sec3_obeysBound17_hostTime

set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

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






/-- A bound with constant one. -/
theorem of_exists_const (hfg : ∃ C : ℝ, ∀ x, dom x → f x ≤ C * g x) (hg : ∀ x, dom x → 0 ≤ g x) :
    Dominated dom f g := by
  obtain ⟨C, hC⟩ := hfg
  exact ⟨|C|, abs_nonneg C, fun x hx =>
    (hC x hx).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (hg x hx))⟩











/-- A constant is `O(g)` when `g ≥ 1` on the domain. -/
protected theorem const (c : ℝ) (hg : ∀ x, dom x → 1 ≤ g x) : Dominated dom (fun _ => c) g :=
  ⟨|c|, abs_nonneg c, fun x hx =>
    (le_abs_self c).trans (le_mul_of_one_le_right (abs_nonneg c) (hg x hx))⟩

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



















/-- `O(g₁) · O(g₂) = O(g₁ g₂)` for nonnegative `f₁`, `f₂`. -/
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
























/-- `n ^ a * n ^ b = n ^ (a + b)` for all large `n`. -/
theorem rpow_mul_rpow_eventuallyEq (a b : ℝ) :
    (fun n : ℕ => (n : ℝ) ^ a * (n : ℝ) ^ b) =ᶠ[atTop] fun n : ℕ => (n : ℝ) ^ (a + b) := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [Real.rpow_add (Nat.cast_pos.2 hn)]

/-- `(log n) ^ e = o(n ^ η)` for `η > 0`. -/
theorem isLittleO_log_pow_rpow {η : ℝ} (hη : 0 < η) (e : ℕ) :
    (fun n : ℕ => Real.log n ^ e) =o[atTop] fun n : ℕ => (n : ℝ) ^ η := by
  have h := (isLittleO_log_rpow_rpow_atTop (e : ℝ) hη).comp_tendsto tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, Real.rpow_natCast] using h

















/-- Logarithms are absorbed: `n ^ a * (log n) ^ e = o(n ^ b)` for `a < b`. -/
theorem isLittleO_rpow_mul_log_pow_rpow {a b : ℝ} (hab : a < b) (e : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) =o[atTop] fun n : ℕ => (n : ℝ) ^ b := by
  have h := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ a) atTop).mul_isLittleO
    (isLittleO_log_pow_rpow (sub_pos.2 hab) e)
  refine h.congr' EventuallyEq.rfl ?_
  simpa only [add_sub_cancel] using rpow_mul_rpow_eventuallyEq a (b - a)

/-- Logarithms are absorbed: `n ^ a * (log n) ^ e = O(n ^ b)` for `a < b`. -/
theorem isBigO_rpow_mul_log_pow_rpow {a b : ℝ} (hab : a < b) (e : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) =O[atTop] fun n : ℕ => (n : ℝ) ^ b :=
  (isLittleO_rpow_mul_log_pow_rpow hab e).isBigO
















end ThreeSumApsp

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

/-- Procedure number i of a list that is appended to the program P₀ has the number |P₀| + i,
whatever is appended after the list. -/
theorem getElem?_append_append {P₀ B : Program} (R : Program) {i : ℕ} {body : Stmt}
    (h : B[i]? = some body) : (P₀ ++ (B ++ R))[P₀.length + i]? = some body := by
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact getElem?_append_of_eq_some h R







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







/-- The sum of two expressions. -/
infixl:65 " +' " => Expr.op Op.add
/-- The difference of two expressions. -/
infixl:65 " -' " => Expr.op Op.sub
/-- The product of two expressions. -/
infixl:70 " *' " => Expr.op Op.mul
@[inherit_doc] infix:50 " <' " => Cond.lt
@[inherit_doc] infix:50 " =' " => Cond.eq
@[inherit_doc] infixr:30 " ;; " => Stmt.seq



@[inherit_doc] infix:50 " ≤' " => Cond.le








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

/-- Brackets do not matter: a piece of several statements, followed by the rest of the program, is
run statement by statement. -/
theorem Ends.seqAssoc {σ : State} {T : ℕ} {s₁ s₂ s₃ : Stmt} {Q : State → Prop}
    (h : Ends lim P d ((Light.Stmt.seq s₁ (Light.Stmt.seq s₂ s₃))) σ T Q) : Ends lim P d ((Light.Stmt.seq (Light.Stmt.seq s₁ s₂) s₃)) σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂₃ =>
    cases he₂₃ with
    | seq he₂ he₃ => exact ⟨σ', _, .seq (.seq he₁ he₂) he₃, by omega, hq⟩

/-- A `skip` before the rest of the program takes no step. -/
theorem Ends.skipThen {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop} (h : Ends lim P d s σ T Q) :
    Ends lim P d ((Light.Stmt.seq .skip s)) σ T Q :=
  Ends.seq 0 T (Ends.skip h) (by omega)

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

/-- From a theorem about a body to the specification. -/
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : Stmt}
    (hp : P[p]? = some body)
    (h : Ends lim P d body ⟨frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩

















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

































































theorem le_timeUpTo (Tn : ℕ → ℕ → ℕ) (n : ℕ) {U : ℕ} {u : ℝ} (hu : (U : ℝ) ≤ u) :
    (Tn n U : ℝ) ≤ timeUpTo Tn n u :=
  Nat.cast_le.2 (Finset.le_sup (f := Tn n)
    (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hu))))

/-- What bounds the time for every natural number `U ≤ u` bounds `timeUpTo`.  For a negative `u`
there is still `U = 0`. -/
theorem timeUpTo_le {Tn : ℕ → ℕ → ℕ} {n : ℕ} {u B : ℝ}
    (h : ∀ U : ℕ, (U : ℝ) ≤ max u 0 → (Tn n U : ℝ) ≤ B) : timeUpTo Tn n u ≤ B := by
  obtain ⟨U, hU, hsup⟩ := Finset.exists_mem_eq_sup (Finset.range (⌊u⌋₊ + 1))
    ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ (Tn n)
  rw [timeUpTo, hsup]
  refine h U ((Nat.cast_le.2 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hU))).trans ?_)
  rcases le_total 0 u with hu | hu
  · exact (Nat.floor_le hu).trans (le_max_left u 0)
  · rw [Nat.floor_of_nonpos hu, Nat.cast_zero]
    exact le_max_right u 0

/-- A solver with a polynomially bounded need solves its task in its own time. -/
theorem Solves.solvedIn {task : Task} {P : Program} {p : ℕ} {Tn : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (hs : Solves task P p Tn need) (hp : PolyNeed need) : SolvedIn task (timeUpTo Tn) :=
  ⟨P, p, Tn, need, hp, hs, fun n _ _ _ _ hu => le_timeUpTo Tn n hu⟩

/-! ## Hosts -/






















/-! ## Tasks with a list of parameters -/























/-- A solver stays a solver when procedures are appended to its program. -/
theorem SolvesN.append {task : TaskN} {P : Program} {p : ℕ} {T : List ℕ → ℕ} {need : List ℕ → Need}
    (h : SolvesN task P p T need) (R : Program) : SolvesN task (P ++ R) p T need := by
  obtain ⟨body, hp, hb⟩ := h
  refine ⟨body, getElem?_append_of_eq_some hp R, fun R' lim d x μ fr hpre hok => ?_⟩
  rw [List.append_assoc]
  exact hb (R ++ R') lim d x μ fr hpre hok

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

/-- Rounding `n ≥ 1` up to a power of `b` costs at most a factor `b`. -/
theorem pow_clog_le_mul {b n : ℕ} (hb : 1 < b) (hn : 1 ≤ n) : b ^ Nat.clog b n ≤ b * n := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hn
  · simp [Nat.clog_one_right, hb.le]
  · have hpos : 0 < Nat.clog b n := Nat.clog_pos hb hn
    have hlt := Nat.pow_pred_clog_lt_self hb hn
    calc b ^ Nat.clog b n = b * b ^ (Nat.clog b n).pred := by
          rw [← Nat.pow_succ', Nat.succ_pred_eq_of_pos hpos]
      _ ≤ b * n := Nat.mul_le_mul_left b hlt.le

end Nat

namespace Real

/-! ## Roots

The `e`-th root of `t` is written `(t : ℝ) ^ ((e : ℝ)⁻¹)`. With these two lemmas,
`Nat.le_floor_iff` and `Nat.ceil_le`, its floor and its ceiling are described by powers of natural
numbers. -/

/-- `x` is at most the `e`-th root of `t` exactly if `x ^ e ≤ t`. -/
theorem natCast_le_rpow_inv_iff {e : ℕ} (he : e ≠ 0) (x t : ℕ) :
    (x : ℝ) ≤ (t : ℝ) ^ ((e : ℝ)⁻¹) ↔ x ^ e ≤ t := by
  rw [Real.le_rpow_inv_iff_of_pos x.cast_nonneg t.cast_nonneg
    (Nat.cast_pos.2 (Nat.pos_of_ne_zero he)), Real.rpow_natCast]
  exact_mod_cast Iff.rfl

/-- The `e`-th root of `t` is at most `x` exactly if `t ≤ x ^ e`. -/
theorem rpow_inv_le_natCast_iff {e : ℕ} (he : e ≠ 0) (x t : ℕ) :
    (t : ℝ) ^ ((e : ℝ)⁻¹) ≤ (x : ℝ) ↔ t ≤ x ^ e := by
  rw [Real.rpow_inv_le_iff_of_pos t.cast_nonneg x.cast_nonneg
    (Nat.cast_pos.2 (Nat.pos_of_ne_zero he)), Real.rpow_natCast]
  exact_mod_cast Iff.rfl

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

































/-- The exponent of Strassen's algorithm: `log₂ 7 < 59 / 21 < 2.81`, because `7 ^ 21 < 2 ^ 59`. -/
theorem logb_two_seven_lt : logb 2 7 < 2.81 := by
  have hpow : ((2 : ℝ) ^ (59 / 21 : ℝ)) ^ 21 = 2 ^ 59 := by
    rw [← rpow_natCast, ← rpow_mul two_pos.le, ← rpow_natCast]
    norm_num
  have hlt : (7 : ℝ) < 2 ^ (59 / 21 : ℝ) :=
    lt_of_pow_lt_pow_left₀ 21 (rpow_nonneg two_pos.le _) (by rw [hpow]; norm_num)
  exact ((logb_lt_iff_lt_rpow one_lt_two (by norm_num)).2 hlt).trans (by norm_num)





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

/-- `n ^ a * (log n) ^ e = Õ(n^a)`. -/
theorem isPowPolylog_rpow_mul_log_pow (a : ℝ) (e : ℕ) :
    IsPowPolylog (fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e) a :=
  ⟨e, isBigO_refl _ _⟩






















namespace IsPowPolylog

































/-- Constant factors are absorbed. -/
theorem const_mul (hf : IsPowPolylog f a) (c : ℝ) : IsPowPolylog (fun n => c * f n) a := by
  obtain ⟨e, hf⟩ := hf
  exact ⟨e, hf.const_mul_left c⟩







































/-- If `f = Õ(n^a)` then `|f| = Õ(n^a)`. -/
protected theorem abs (hf : IsPowPolylog f a) : IsPowPolylog (fun n => |f n|) a := by
  obtain ⟨e, hf⟩ := hf
  exact ⟨e, hf.norm_left⟩






/-- Logarithms are absorbed: `Õ(n^a) ⊆ O(n^b)` for `a < b`. -/
theorem isBigOPow (hf : IsPowPolylog f a) (hab : a < b) : IsBigOPow f b := by
  obtain ⟨e, hf⟩ := hf
  exact hf.trans (isBigO_rpow_mul_log_pow_rpow hab e)







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

/-- `f = O(n^a)` is in particular an upper bound on `f`. -/
theorem IsBigOPow.upperBigOPow (hf : IsBigOPow f a) : UpperBigOPow f a := by
  obtain ⟨C, hC⟩ := IsBigO.bound hf
  refine ⟨C, hC.mono fun n hn => ?_⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg n.cast_nonneg a)] at hn
  exact (le_abs_self _).trans hn

namespace UpperBigOPow

/-- The function may be replaced by one that is eventually at most as large. -/
theorem mono_left (h : UpperBigOPow f a) (hle : ∀ᶠ n in atTop, f' n ≤ f n) : UpperBigOPow f' a := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, (hle.and hC).mono fun n hn => hn.1.trans hn.2⟩

end UpperBigOPow

/-! ### `Õ(n^a)` from above -/











namespace UpperPowPolylog







/-- An upper bound `Õ(n^a)` is a bound by a nonnegative function of the class `Õ(n^a)`. -/
theorem exists_isPowPolylog (h : UpperPowPolylog f a) :
    ∃ g : ℕ → ℝ, (∀ n, 0 ≤ g n) ∧ IsPowPolylog g a ∧ ∀ᶠ n in atTop, f n ≤ g n := by
  obtain ⟨C, e, hC⟩ := h
  exact ⟨fun n => |C * ((n : ℝ) ^ a * Real.log n ^ e)|, fun n => abs_nonneg _,
    ((isPowPolylog_rpow_mul_log_pow a e).const_mul C).abs,
    hC.mono fun n hn => hn.trans (le_abs_self _)⟩



































/-- Logarithms are absorbed: `Õ(n^a) ⊆ O(n^b)` for `a < b`, from above. -/
theorem upperBigOPow (h : UpperPowPolylog f a) (hab : a < b) : UpperBigOPow f b := by
  obtain ⟨g, -, hg, hfg⟩ := h.exists_isPowPolylog
  exact (hg.isBigOPow hab).upperBigOPow.mono_left hfg

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









theorem mon_zero (x : α) : s.mon 0 x = 1 := by simp [mon]

theorem mon_add (e e' : ι → ℕ) (x : α) : s.mon (e + e') x = s.mon e x * s.mon e' x := by
  simp only [mon, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem mon_smul (k : ℕ) (e : ι → ℕ) (x : α) : s.mon (k • e) x = s.mon e x ^ k := by
  simp only [mon, Pi.smul_apply, smul_eq_mul, ← Finset.prod_pow, ← pow_mul, mul_comm k]

theorem mon_single [DecidableEq ι] (i : ι) (x : α) : s.mon (Pi.single i 1) x = s.base i x := by
  simp [mon, Pi.single_apply, pow_ite]

variable {s} {x : α} {e e' : ι → ℕ} {c c' : ℕ}

/-- All bases are at least 1, so a monomial grows with its exponents. -/
theorem mon_le_mon (he : ∀ i, e i ≤ e' i) (hx : s.dom x) : s.mon e x ≤ s.mon e' x :=
  Finset.prod_le_prod (fun i _ => pow_nonneg (zero_le_one.trans (s.one_le_base i x hx)) _)
    fun i _ => pow_le_pow_right₀ (s.one_le_base i x hx) (he i)

/-- A monomial is at least 1. -/
theorem one_le_mon (e : ι → ℕ) (hx : s.dom x) : 1 ≤ s.mon e x :=
  (s.mon_zero x).ge.trans (mon_le_mon (fun _ => Nat.zero_le _) hx)

/-- The bound grows with all exponents. -/
theorem pow_mul_mon_le (hc : c ≤ c') (he : ∀ i, e i ≤ e' i) (hx : s.dom x) :
    s.hidden x ^ c * s.mon e x ≤ s.hidden x ^ c' * s.mon e' x :=
  mul_le_mul (pow_le_pow_right₀ (s.one_le_hidden x hx) hc) (mon_le_mon he hx)
    (zero_le_one.trans (one_le_mon e hx)) (pow_nonneg (zero_le_one.trans (s.one_le_hidden x hx)) _)

namespace SoftO

variable {t t₁ t₂ : α → ℕ} {e₁ e₂ : ι → ℕ}

/-! ### Entering and leaving -/

/-- A count that is at most `hidden`. -/
theorem of_le_hidden (h : ∀ x, s.dom x → (t x : ℝ) ≤ s.hidden x) : s.SoftO t 0 :=
  ⟨1, .of_le fun x hx => by simpa only [pow_one, mon_zero, mul_one] using h x hx⟩

/-- A count that is at most a constant times a base. -/
theorem of_dominated_base [DecidableEq ι] (i : ι)
    (h : Dominated s.dom (fun x => (t x : ℝ)) (s.base i)) : s.SoftO t (Pi.single i 1) :=
  ⟨0, h.congr (fun _ _ => rfl) fun x _ => by rw [pow_zero, mon_single, one_mul]⟩

/-- A count that is at most a base. -/
theorem of_le_base [DecidableEq ι] (i : ι) (h : ∀ x, s.dom x → (t x : ℝ) ≤ s.base i x) :
    s.SoftO t (Pi.single i 1) :=
  of_dominated_base i (.of_le h)

/-- A count that is at most a constant times a monomial. -/
theorem of_dominated (h : Dominated s.dom (fun x => (t x : ℝ)) (s.mon e)) : s.SoftO t e :=
  ⟨0, by simpa only [pow_zero, one_mul] using h⟩

/-- The bound, written out. -/
theorem exists_le (h : s.SoftO t e) :
    ∃ (C : ℝ) (c : ℕ), 0 ≤ C ∧ ∀ x, s.dom x → (t x : ℝ) ≤ C * (s.hidden x ^ c * s.mon e x) :=
  let ⟨c, C, hC, hle⟩ := h
  ⟨C, c, hC, hle⟩

/-- If `hidden = 1`, the bound is the monomial. -/
theorem dominated (h : s.SoftO t e) (hhidden : ∀ x, s.dom x → s.hidden x = 1) :
    Dominated s.dom (fun x => (t x : ℝ)) (s.mon e) :=
  let ⟨_, h⟩ := h
  h.congr (fun _ _ => rfl) fun x hx => by rw [hhidden x hx, one_pow, one_mul]

/-! ### The rules -/

/-- The exponents may be raised. -/
theorem mono (h : s.SoftO t e) (he : ∀ i, e i ≤ e' i) : s.SoftO t e' :=
  let ⟨c, h⟩ := h
  ⟨c, h.mono_right fun _ hx => pow_mul_mon_le le_rfl he hx⟩

/-- A smaller count has the same bound. -/
theorem of_le (h : s.SoftO t₂ e) (hle : ∀ x, s.dom x → t₁ x ≤ t₂ x) : s.SoftO t₁ e :=
  let ⟨c, h⟩ := h
  ⟨c, h.mono_left fun x hx => Nat.cast_le.2 (hle x hx)⟩

/-- A quantity `f` that is at most `g` everywhere has the bound of `g`, at any argument. -/
theorem of_forall_le {β : Type*} {f g : β → ℕ} (hle : ∀ y, f y ≤ g y) {u : α → β}
    (h : s.SoftO (fun x => g (u x)) e) : s.SoftO (fun x => f (u x)) e :=
  h.of_le fun _ _ => hle _

/-- A quantity `f` with two arguments that is at most `g` everywhere has the bound of `g`. -/
theorem of_forall_le₂ {β γ : Type*} {f g : β → γ → ℕ} (hle : ∀ y z, f y z ≤ g y z) {u : α → β}
    {v : α → γ} (h : s.SoftO (fun x => g (u x) (v x)) e) : s.SoftO (fun x => f (u x) (v x)) e :=
  h.of_le fun _ _ => hle _ _

/-- A constant has the exponents 0. -/
protected theorem const (k : ℕ) : s.SoftO (fun _ => k) 0 :=
  ⟨0, .const _ fun x _ => by rw [pow_zero, mon_zero, mul_one]⟩

/-- A sum has the larger exponents. -/
protected theorem add (h₁ : s.SoftO t₁ e₁) (h₂ : s.SoftO t₂ e₂) :
    s.SoftO (fun x => t₁ x + t₂ x) (e₁ ⊔ e₂) := by
  obtain ⟨c₁, h₁⟩ := h₁
  obtain ⟨c₂, h₂⟩ := h₂
  refine ⟨max c₁ c₂, ?_⟩
  simpa only [Nat.cast_add] using
    (h₁.mono_right fun _ hx =>
      pow_mul_mon_le (e' := e₁ ⊔ e₂) (le_max_left _ _) (fun _ => le_sup_left) hx).add
      (h₂.mono_right fun _ hx => pow_mul_mon_le (le_max_right _ _) (fun _ => le_sup_right) hx)





/-- In a product the exponents add up. -/
protected theorem mul (h₁ : s.SoftO t₁ e₁) (h₂ : s.SoftO t₂ e₂) :
    s.SoftO (fun x => t₁ x * t₂ x) (e₁ + e₂) := by
  obtain ⟨c₁, h₁⟩ := h₁
  obtain ⟨c₂, h₂⟩ := h₂
  refine ⟨c₁ + c₂, ?_⟩
  simpa only [Nat.cast_mul] using
    (h₁.mul h₂ (fun _ _ => Nat.cast_nonneg _) fun _ _ => Nat.cast_nonneg _).congr (fun _ _ => rfl)
      fun x _ => by rw [mon_add, pow_add, mul_mul_mul_comm]

/-- The `k`-th power multiplies the exponents by `k`. -/
protected theorem pow (h : s.SoftO t e) (k : ℕ) : s.SoftO (fun x => t x ^ k) (k • e) := by
  obtain ⟨c, h⟩ := h
  refine ⟨c * k, ?_⟩
  simpa only [Nat.cast_pow] using
    (h.pow (fun _ _ => Nat.cast_nonneg _) k).congr (fun _ _ => rfl)
      fun x _ => by rw [mon_smul, mul_pow, pow_mul]

/-- A maximum has the larger exponents. -/
protected theorem max (h₁ : s.SoftO t₁ e₁) (h₂ : s.SoftO t₂ e₂) :
    s.SoftO (fun x => max (t₁ x) (t₂ x)) (e₁ ⊔ e₂) :=
  (h₁.add h₂).of_le fun _ _ => max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)









/-- A quotient that is rounded up has the larger exponents of numerator and denominator. -/
protected theorem ceilDiv (h₁ : s.SoftO t₁ e₁) (h₂ : s.SoftO t₂ e₂) :
    s.SoftO (fun x => t₁ x ⌈/⌉ t₂ x) (e₁ ⊔ e₂) :=
  (h₁.add h₂).of_le fun _ _ =>
    (Nat.ceilDiv_eq_add_pred_div _ _).trans_le ((Nat.div_le_self _ _).trans (Nat.sub_le _ _))

/-- A logarithm is at most the number. -/
protected theorem log (h : s.SoftO t e) (b : ℕ) : s.SoftO (fun x => Nat.log b (t x)) e :=
  h.of_le fun _ _ => Nat.log_le_self _ _

/-- A square root is at most the number. -/
protected theorem sqrt (h : s.SoftO t e) : s.SoftO (fun x => Nat.sqrt (t x)) e :=
  h.of_le fun _ _ => Nat.sqrt_le_self _




































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

/-- The size `n` is polynomially bounded. -/
theorem fst : PolyBounded (fun n _ => n) :=
  (Scale.SoftO.of_le_hidden fun p _ => Nat.cast_le.2 <|
    (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ p.2.succ_pos)).mono (by decide)

/-- The bound `U` is polynomially bounded. -/
theorem snd : PolyBounded (fun _ U => U) :=
  (Scale.SoftO.of_le_hidden fun p _ => Nat.cast_le.2 <|
    (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ p.1.succ_pos)).mono (by decide)

/-- A smaller function has the same bound. -/
theorem of_le {G : ℕ → ℕ → ℕ} (h : PolyBounded G) (hle : ∀ n U, F n U ≤ G n U) : PolyBounded F :=
  Scale.SoftO.of_le h fun _ _ => hle _ _

/-- The bound with natural numbers. -/
theorem exists_nat_le (h : PolyBounded F) :
    ∃ K e : ℕ, ∀ n U, F n U ≤ K * ((n + 1) * (U + 1)) ^ e := by
  obtain ⟨C, e, hC, hle⟩ := h.exists_le
  refine ⟨⌈C⌉₊, e, fun n U => ?_⟩
  have hceil : (F n U : ℝ) ≤ ⌈C⌉₊ * (((n + 1) * (U + 1) : ℕ) : ℝ) ^ e := by
    simpa [polyScale, Scale.mon] using (hle (n, U) trivial).trans
      (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (by simp [polyScale, Scale.mon]; positivity))
  exact_mod_cast hceil

end PolyBounded






namespace PolyBounded







/-- Three polynomially bounded functions make a polynomially bounded need. -/
theorem polyNeed {need : ℕ → ℕ → Need} (hw : PolyBounded fun n U => (need n U).word)
    (hc : PolyBounded fun n U => (need n U).cells) (hd : PolyBounded fun n U => (need n U).depth) :
    PolyNeed need := by
  obtain ⟨K, e, hK⟩ := exists_nat_le (F := fun n U => (need n U).word + (need n U).cells +
    (need n U).depth) (by first
                          |
                            ((apply ThreeSumApsp.Scale.SoftO.mono);
                              (·
                                  repeat'
                                    with_reducible
                                      first
                                      | exact ThreeSumApsp.Scale.SoftO.const _
                                      | apply Light.PolyBounded.fst
                                      | apply Light.PolyBounded.snd
                                      | apply ThreeSumApsp.Scale.SoftO.log
                                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                                      | apply hw
                                      | apply hc
                                      | apply hd
                                      | apply ThreeSumApsp.Scale.SoftO.add
                                      | apply ThreeSumApsp.Scale.SoftO.mul
                                      | apply ThreeSumApsp.Scale.SoftO.pow
                                      | apply ThreeSumApsp.Scale.SoftO.max
                                      | apply ThreeSumApsp.Scale.SoftO.sub
                                      | apply ThreeSumApsp.Scale.SoftO.div);
                              (·
                                  first
                                  | decide
                                  | exact isEmptyElim))
                          |
                            ((fail_if_success
                                  (fail_if_success
                                      ((apply ThreeSumApsp.Scale.SoftO.mono);
                                        (on_goal 1 =>
                                            ((repeat'
                                                  with_reducible
                                                    first
                                                    | exact ThreeSumApsp.Scale.SoftO.const _
                                                    | apply Light.PolyBounded.fst
                                                    | apply Light.PolyBounded.snd
                                                    | apply ThreeSumApsp.Scale.SoftO.log
                                                    | apply ThreeSumApsp.Scale.SoftO.sqrt
                                                    | apply hw
                                                    | apply hc
                                                    | apply hd
                                                    | apply ThreeSumApsp.Scale.SoftO.add
                                                    | apply ThreeSumApsp.Scale.SoftO.mul
                                                    | apply ThreeSumApsp.Scale.SoftO.pow
                                                    | apply ThreeSumApsp.Scale.SoftO.max
                                                    | apply ThreeSumApsp.Scale.SoftO.sub
                                                    | apply ThreeSumApsp.Scale.SoftO.div);
                                              (done))))));
                              (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
                              (all_goals
                                  try
                                    ((apply ThreeSumApsp.Scale.SoftO.mono);
                                      (·
                                          repeat'
                                            with_reducible
                                              first
                                              | exact ThreeSumApsp.Scale.SoftO.const _
                                              | apply Light.PolyBounded.fst
                                              | apply Light.PolyBounded.snd
                                              | apply ThreeSumApsp.Scale.SoftO.log
                                              | apply ThreeSumApsp.Scale.SoftO.sqrt
                                              | apply hw
                                              | apply hc
                                              | apply hd
                                              | apply ThreeSumApsp.Scale.SoftO.add
                                              | apply ThreeSumApsp.Scale.SoftO.mul
                                              | apply ThreeSumApsp.Scale.SoftO.pow
                                              | apply ThreeSumApsp.Scale.SoftO.max
                                              | apply ThreeSumApsp.Scale.SoftO.sub
                                              | apply ThreeSumApsp.Scale.SoftO.div);
                                      (· decide))))
                          |
                            ((apply ThreeSumApsp.Scale.SoftO.mono);
                              (·
                                  repeat'
                                    with_reducible
                                      first
                                      | exact ThreeSumApsp.Scale.SoftO.const _
                                      | apply Light.PolyBounded.fst
                                      | apply Light.PolyBounded.snd
                                      | apply ThreeSumApsp.Scale.SoftO.log
                                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                                      | apply hw
                                      | apply hc
                                      | apply hd
                                      | apply ThreeSumApsp.Scale.SoftO.add
                                      | apply ThreeSumApsp.Scale.SoftO.mul
                                      | apply ThreeSumApsp.Scale.SoftO.pow
                                      | apply ThreeSumApsp.Scale.SoftO.max
                                      | apply ThreeSumApsp.Scale.SoftO.sub
                                      | apply ThreeSumApsp.Scale.SoftO.div)))
  refine ⟨Nat.size K, e, fun n U => ?_⟩
  have hsum := hK n U
  have hpoly : K * ((n + 1) * (U + 1)) ^ e ≤ Light.polyBound (Nat.size K) e [n, U] := by
    simp only [Light.polyBound, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact Nat.mul_le_mul_right _ (Nat.lt_size_self K).le
  exact ⟨by omega, by omega, by omega⟩

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

























/-- The second term of the bound of Corollaries 16 and 26 is at most the bound. -/
theorem sq_div_rpow_le_wantedBound (n D w : ℕ) :
    (n : ℝ) ^ 2 / (D : ℝ) ^ (0.063 : ℝ) ≤ wantedBound n D w :=
  le_add_of_nonneg_left (by positivity)

/-- `1 ≤ w D^{0.437} + n² / D^{0.063}`. -/
theorem one_le_wantedBound {n D : ℕ} (hD : 1 ≤ D) (hDn : D ^ 18 ≤ n) (w : ℕ) :
    1 ≤ wantedBound n D w :=
  (one_le_sq_div_rpow hD hDn (by norm_num)).trans (sq_div_rpow_le_wantedBound n D w)

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

/-- The scratch space, exactly. -/
theorem strScr_add (p j : ℕ) : strScr p j + p = 4 ^ j * p := by
  induction j with
  | zero => simp [strScr]
  | succ j ih =>
    rw [strScr, pow_succ]
    have : 4 ^ j * 4 * p = 4 * (4 ^ j * p) := by ring
    omega

/-- The scratch space is at most the size of an operand. -/
theorem strScr_le (p j : ℕ) : strScr p j ≤ 4 ^ j * p := by
  have := strScr_add p j
  omega
























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







/-- The power of `rootFloor e t` does not exceed `t`. -/
theorem rootFloor_pow_le {e : ℕ} (he : e ≠ 0) (t : ℕ) : rootFloor e t ^ e ≤ t :=
  Nat.findGreatest_spec (P := fun x => x ^ e ≤ t) (Nat.zero_le t) (by simp [he])

/-- `rootFloor e t` is the greatest `x` with `x^e ≤ t`. -/
theorem le_rootFloor {e : ℕ} (he : e ≠ 0) {t x : ℕ} (h : x ^ e ≤ t) : x ≤ rootFloor e t :=
  Nat.le_findGreatest ((Nat.le_self_pow he x).trans h) h

/-- The characterisation of `rootFloor` by which a program finds it. -/
theorem le_rootFloor_iff {e : ℕ} (he : e ≠ 0) {t x : ℕ} : x ≤ rootFloor e t ↔ x ^ e ≤ t :=
  ⟨fun h => (Nat.pow_le_pow_left h e).trans (rootFloor_pow_le he t), le_rootFloor he⟩

/-- `rootFloor e t` is `⌊t^{1/e}⌋`. -/
theorem floor_rpow_inv {e : ℕ} (he : e ≠ 0) (t : ℕ) :
    ⌊(t : ℝ) ^ ((e : ℝ)⁻¹)⌋₊ = rootFloor e t := by
  refine eq_of_forall_le_iff fun x => ?_
  rw [Nat.le_floor_iff (by positivity), Real.natCast_le_rpow_inv_iff he, le_rootFloor_iff he]

/-- The power of `rootCeil e t` reaches `t`. -/
theorem le_rootCeil_pow {e : ℕ} (he : e ≠ 0) (t : ℕ) : t ≤ rootCeil e t ^ e := by
  unfold rootCeil
  set G := Nat.findGreatest (fun g => g ^ e < t) t
  rcases Nat.lt_or_ge t (G + 1) with h | h
  · exact h.le.trans (Nat.le_self_pow he _)
  · exact not_lt.1 (Nat.findGreatest_is_greatest (P := fun g => g ^ e < t) (Nat.lt_succ_self G) h)

/-- `rootCeil e t` is the least `g` with `t ≤ g^e`, for `t ≥ 1`. -/
theorem rootCeil_le {e : ℕ} (he : e ≠ 0) {t g : ℕ} (ht : 1 ≤ t) (h : t ≤ g ^ e) :
    rootCeil e t ≤ g := by
  have hspec : Nat.findGreatest (fun g => g ^ e < t) t ^ e < t :=
    Nat.findGreatest_spec (P := fun g => g ^ e < t) (Nat.zero_le t)
      (show 0 ^ e < t by rw [zero_pow he]; exact ht)
  exact lt_of_pow_lt_pow_left₀ e (Nat.zero_le g) (hspec.trans_le h)

/-- The characterisation of `rootCeil` by which a program finds it. -/
theorem rootCeil_le_iff {e : ℕ} (he : e ≠ 0) {t g : ℕ} (ht : 1 ≤ t) :
    rootCeil e t ≤ g ↔ t ≤ g ^ e :=
  ⟨fun h => (le_rootCeil_pow he t).trans (Nat.pow_le_pow_left h e), rootCeil_le he ht⟩

/-- `rootCeil e t` is `⌈t^{1/e}⌉`, for `t ≥ 1`. -/
theorem ceil_rpow_inv {e : ℕ} (he : e ≠ 0) {t : ℕ} (ht : 1 ≤ t) :
    ⌈(t : ℝ) ^ ((e : ℝ)⁻¹)⌉₊ = rootCeil e t := by
  refine eq_of_forall_ge_iff fun g => ?_
  rw [Nat.ceil_le, Real.rpow_inv_le_natCast_iff he, rootCeil_le_iff he ht]

/-! ## The parameters of the proof of Theorem 19 -/













/-- `⌊n^{1/18}⌋`, with the exponent as the paper writes it. -/
private theorem floor_rpow_one_div (n : ℕ) : ⌊(n : ℝ) ^ (1 / 18 : ℝ)⌋₊ = rootFloor 18 n := by
  rw [← floor_rpow_inv (by norm_num)]
  norm_num

/-- "Let D := ⌊n^{1/18}⌋". -/
theorem paramD₂₆Nat_eq (n : ℕ) : paramD₂₆Nat n = paramD₂₆ n := (floor_rpow_one_div n).symm

/-- `⌊n^{1/18}⌋ ≤ n`. -/
theorem paramD₂₆Nat_le (n : ℕ) : paramD₂₆Nat n ≤ n := Nat.findGreatest_le n

/-- `⌊n^{1/18}⌋ ≥ 1` for `n ≥ 1`. -/
theorem one_le_paramD₂₆Nat {n : ℕ} (hn : 1 ≤ n) : 1 ≤ paramD₂₆Nat n :=
  le_rootFloor (by norm_num) (by simpa using hn)




































/-- "and g := ⌈D^{0.0315}⌉". -/
theorem paramG₂₆Nat_eq {n : ℕ} (hn : 1 ≤ n) : paramG₂₆Nat (paramD₂₆ n) = paramG₂₆ n := by
  have hD : 1 ≤ paramD₂₆ n := paramD₂₆Nat_eq n ▸ one_le_paramD₂₆Nat hn
  rw [paramG₂₆Nat, paramG₂₆, ← ceil_rpow_inv (by norm_num) (Nat.one_le_pow _ _ hD)]
  congr 1
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num





/-- `⌈D^{0.0315}⌉ ≤ D`. -/
theorem paramG₂₆Nat_le {D : ℕ} (hD : 1 ≤ D) : paramG₂₆Nat D ≤ D :=
  rootCeil_le (by norm_num) (Nat.one_le_pow _ _ hD) (pow_le_pow_right₀ hD (by norm_num))

/-! ## The sizes of the instances of the proof of Theorem 17 -/







































































end ThreeSumApsp.Spec

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







/-- One more factor. -/
theorem capPow_succ (g t i : ℕ) :
    capPow g t (i + 1) = if capPow g t i < t then capPow g t i * g else capPow g t i := rfl

/-- Below t the value is the power, and a value that has reached t shows that the power has. -/
theorem capPow_spec {g : ℕ} (hg : 1 ≤ g) (t i : ℕ) :
    (capPow g t i < t → capPow g t i = g ^ i) ∧ (t ≤ capPow g t i → t ≤ g ^ i) := by
  induction i with
  | zero => simp [capPow]
  | succ i ih =>
    rw [capPow_succ]
    split_ifs with h
    · rw [ih.1 h, pow_succ]
      exact ⟨fun _ => rfl, fun h' => h'⟩
    · exact ⟨fun h' => absurd h' h,
        fun _ => (ih.2 (not_lt.1 h)).trans (Nat.pow_le_pow_right hg (Nat.le_succ i))⟩

/-- The value is below t exactly if the power is. -/
theorem capPow_lt_iff {g : ℕ} (hg : 1 ≤ g) (t i : ℕ) : capPow g t i < t ↔ g ^ i < t := by
  obtain ⟨hlow, hhigh⟩ := capPow_spec hg t i
  exact ⟨fun h => hlow h ▸ h, fun h => not_le.1 fun hc => absurd (hhigh hc) (not_le.2 h)⟩

namespace PowLt









end PowLt











/-- **powLt**, for g ≥ 1, returns 1 if g^e < t and 0 if not, in at most 16 e + 14 steps.  It forms
no number above t g + e + 1. -/
theorem powLt_meets {μ : ℕ → ℤ} {pPow g e t : ℕ} (hP : P[pPow]? = some powLtBody) (hg : 1 ≤ g)
    (hword : ((t * g + e + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pPow d [g, e, t] μ (16 * e + 14) fun r μ' =>
      r = (if g ^ e < t then 1 else 0) ∧ μ' = μ := by
  refine .of_body hP ?_
  push_cast at hword
  have htg : (0 : ℤ) ≤ (t : ℤ) * g := by positivity
  -- cnt := 0; prod := 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
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
          (1 : ℕ)
            -- while cnt < e.  Before round i, cnt = i and prod = capPow g t i.
            
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
  -- while cnt < e.  Before round i, cnt = i and prod = capPow g t i.
  refine Ends.next _ (Ends.whileBlock
    (fun i σ => σ = ⟨frame [g, e, t, i, (capPow g t i : ℕ)], μ⟩) e (by simp [capPow]) ?round ?done
    le_rfl) (by simp; omega)
  case round =>
    rintro i _ hi rfl
    rw [capPow_succ]
    generalize capPow g t i = c
    -- if prod < t then prod := prod * g; cnt := cnt + 1
    by_cases hlt : c < t
    · have hmul : (c : ℤ) * g ≤ t * g := by exact_mod_cast Nat.mul_le_mul_right g hlt.le
      have hmul0 : (0 : ℤ) ≤ (c : ℤ) * g := by positivity
      exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                    ((try have := Light.Std.const_le (by assumption)));
                    (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                    ((try have := Light.Std.const_le (by assumption)));
                                                                                    (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                                                                                    ((try have := Light.Std.const_le (by assumption)));
                                                                                                                                                    (simp [Light.Limits.Addr, abs_le, -abs_mul, hlt] <;> omega)),
        by simp [update_frame_setLocal, hlt]⟩
    · exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                     ((try have := Light.Std.const_le (by assumption)));
                     (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                     ((try have := Light.Std.const_le (by assumption)));
                                                                                     (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp [abs_le, hlt]; omega,
        by simp [update_frame_setLocal, hlt]⟩
  case done =>
    rintro _ rfl
    have hiff := capPow_lt_iff hg t e
    -- return 1 if prod < t, and 0 if not
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                   ((try have := Light.Std.const_le (by assumption)));
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)),
      Ends.iteLast (fun h => ?_) (fun h => ?_) (hT := by simp; omega)⟩
    · have hlt : g ^ e < t := hiff.1 (by simpa using h)
      exact Ends.setTo 1 (by simp [hlt]) (hT := by simp; omega)
    · have hlt : ¬ g ^ e < t := fun h' => h (by simpa using hiff.2 h')
      exact Ends.setTo 0 (by simp [hlt]) (hT := by simp; omega)

/-! ## Roots, rounded up -/

namespace RootCeil







end RootCeil














/-- **rootCeil** returns the least g with g^e ≥ t, for e ≥ 1 and t ≥ 1.  It forms no number above t
times the result plus e + 1. -/
theorem rootCeil_meets {μ : ℕ → ℤ} {pRoot pPow e t : ℕ} (hR : P[pRoot]? = some (rootCeilBody pPow))
    (hP : P[pPow]? = some powLtBody) (he : e ≠ 0) (ht : 1 ≤ t)
    (hword : ((t * rootCeil e t + e + 1 : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim P pRoot d [e, t] μ (tRootCeil e t) fun r μ' => r = (rootCeil e t : ℕ) ∧ μ' = μ := by
  refine .of_body hR ?_
  have key : ∀ g, g ^ e < t ↔ g < rootCeil e t := fun g => by
    rw [← not_le, ← not_le, rootCeil_le_iff he ht]
  have hpos : 1 ≤ rootCeil e t := Nat.succ_le_succ (Nat.zero_le _)
  unfold tRootCeil
  generalize rootCeil e t = G at key hpos hword
  obtain ⟨y, rfl⟩ : ∃ y, G = y + 1 := ⟨G - 1, by omega⟩
  have hyt : y + 1 ≤ t * (y + 1) := Nat.le_mul_of_pos_left _ ht
  -- The test of a candidate g ≤ y + 1.
  have test : ∀ g, 1 ≤ g → g ≤ y + 1 → Meets lim P pPow (d + 1) [g, e, t] μ (16 * e + 14)
      fun r μ' => r = (if g < y + 1 then 1 else 0) ∧ μ' = μ := fun g hg hgy => by
    have hle : t * g + e + 1 ≤ t * (y + 1) + e + 1 := by
      have := Nat.mul_le_mul_left t hgy
      omega
    simpa only [key] using powLt_meets hP hg ((Int.ofNat_le.2 hle).trans hword)
  -- cand := 1; more := powLt(cand, e, t)
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (1 : ℕ) ?_ ?_ ?_);
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
    (first
      |
        refine
          Light.Ends.callToThen ((test 1 le_rfl hpos) _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen (test 1 le_rfl hpos) ?_ ?_ ?_ ?_);
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
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro _ μ' ⟨rfl, hμ⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  rw [hμ]
  -- while more = 1.  Before round i, cand = i + 1.
  refine Ends.next _ (Ends.whileConst
    (fun i σ => σ = ⟨frame [e, t, (i + 1 : ℕ), if i + 1 < y + 1 then 1 else 0], μ⟩) y (16 * e + 23)
    (by simp) ?round ?done le_rfl) (by simp; ring_nf; omega)
  case round =>
    rintro i _ hi rfl
    -- cand := cand + 1; more := powLt(cand, e, t)
    refine ⟨by (((try have := Light.Std.space_le (by assumption)));
                   ((try have := Light.Std.const_le (by assumption)));
                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp [hi], Ends.setToThen (i + 1 + 1 : ℕ)
      (Ends.callTo (test (i + 1 + 1) (by omega) (by omega)) ?_)⟩
    rintro _ μ' ⟨rfl, hμ⟩
    simp [hμ]
  case done =>
    rintro _ rfl
    -- return cand
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by simp, Ends.setTo (y + 1 : ℕ) (by simp) (hT := by simp; ring_nf; omega)⟩

/-- Rounding a root down is rounding the root of the next number up, minus one. -/
theorem rootCeil_succ {e : ℕ} (he : e ≠ 0) (t : ℕ) : rootCeil e (t + 1) = rootFloor e t + 1 := by
  have h : ∀ g, rootCeil e (t + 1) ≤ g ↔ rootFloor e t + 1 ≤ g := fun g => by
    rw [rootCeil_le_iff he (by omega), Nat.succ_le_iff, Nat.succ_le_iff, ← not_le, ← not_le,
      le_rootFloor_iff he]
  exact le_antisymm ((h _).2 le_rfl) ((h _).1 le_rfl)

/-! ## The four parameters of the proof of Theorem 19 -/










/-- **d26** returns ⌊n^{1/18}⌋. -/
theorem d26_spec {μ : ℕ → ℤ} {pRoot pPow n : ℕ} (hR : P[pRoot]? = some (rootCeilBody pPow))
    (hP : P[pPow]? = some powLtBody)
    (hword : (((n + 1) * (paramD₂₆Nat n + 1) + 19 : ℕ) : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth) :
    Ends lim P d (d26Body pRoot) ⟨frame [n], μ⟩ (tD26 n) fun σ' =>
      σ'.loc 0 = (paramD₂₆Nat n : ℕ) ∧ σ'.mem = μ := by
  have hroot : rootCeil 18 (n + 1) = paramD₂₆Nat n + 1 := rootCeil_succ (by norm_num) n
  have hn : n + 1 ≤ (n + 1) * (paramD₂₆Nat n + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hD : paramD₂₆Nat n + 1 ≤ (n + 1) * (paramD₂₆Nat n + 1) := Nat.le_mul_of_pos_left _ (by omega)
  -- root := rootCeil(18, n + 1)
  refine Ends.callToThen (rootCeil_meets (e := 18) (t := n + 1) hR hP (by norm_num) (by omega)
    (by rw [hroot]; exact hword) (by omega)) ?_ (hT := by simp [tD26, tRootCeil, hroot]; omega)
  rintro _ μ' ⟨rfl, hμ⟩
  -- return root - 1
  rw [hroot, hμ]
  exact Ends.setTo (paramD₂₆Nat n) (by simp) (hT := by simp [tD26, tRootCeil, hroot]; omega)



































































































/-- **g26** returns ⌈D^{0.0315}⌉, for D ≥ 1. -/
theorem g26_spec {μ : ℕ → ℤ} {pRoot pPow D : ℕ} (hR : P[pRoot]? = some (rootCeilBody pPow))
    (hP : P[pPow]? = some powLtBody) (hD : 1 ≤ D)
    (hword : ((D ^ 63 * paramG₂₆Nat D + 2001 : ℕ) : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth) :
    Ends lim P d (g26Body pRoot) ⟨frame [D], μ⟩ (tG26 D) fun σ' =>
      σ'.loc 0 = (paramG₂₆Nat D : ℕ) ∧ σ'.mem = μ := by
  have hpos : 1 ≤ paramG₂₆Nat D := Nat.succ_le_succ (Nat.zero_le _)
  have hfits : ((D ^ 63 + 2001 : ℕ) : ℤ) ≤ lim.word := le_trans
    (by exact_mod_cast Nat.add_le_add_right (Nat.le_mul_of_pos_right _ hpos) 2001) hword
  rw [Nat.cast_add] at hfits
  have hpow0 : (0 : ℤ) ≤ ((D ^ 63 : ℕ) : ℤ) := Int.natCast_nonneg _
  unfold tG26
  -- cnt := 0; prod := 1
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_);
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
          (1 : ℕ)
            -- while cnt < 63: prod := prod * D; cnt := cnt + 1.  Before round i, prod = D^i.
            
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
  -- while cnt < 63: prod := prod * D; cnt := cnt + 1.  Before round i, prod = D^i.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [D, i, (D ^ i : ℕ)], μ⟩) 63 (by simp)
    ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hle : ((D ^ (i + 1) : ℕ) : ℤ) ≤ ((D ^ 63 : ℕ) : ℤ) := by
      exact_mod_cast Nat.pow_le_pow_right hD hi
    have hmul : ((D ^ i : ℕ) : ℤ) * D = ((D ^ (i + 1) : ℕ) : ℤ) := by push_cast; ring
    have hmul0 : (0 : ℤ) ≤ ((D ^ (i + 1) : ℕ) : ℤ) := Int.natCast_nonneg _
    generalize ((D ^ (i + 1) : ℕ) : ℤ) = q' at hle hmul hmul0
    generalize ((D ^ i : ℕ) : ℤ) = q at hmul
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, hmul] <;> omega)),
      by simp [update_frame_setLocal, hmul]⟩
  case done =>
    rintro _ rfl
    -- return rootCeil(2000, prod)
    exact ⟨by (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)), by (((try have := Light.Std.space_le (by assumption)));
                                                                                  ((try have := Light.Std.const_le (by assumption)));
                                                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)),
      Ends.callTo (rootCeil_meets (e := 2000) (t := D ^ 63) hR hP (by norm_num)
        (Nat.one_le_pow _ _ hD) hword (by omega)) (fun r μ' h => by simpa [paramG₂₆Nat] using h)
        (hT := by simp [tRootCeil, paramG₂₆Nat]; omega)⟩

/-! ## ⌊n²/√D⌋ and quotients rounded up -/












































































































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

/-- `⌊n²/√D⌋ ≤ n²`. -/
private theorem queryCapNat_le_sq (n D : ℕ) : queryCapNat n D ≤ n ^ 2 := by
  unfold queryCapNat
  calc Nat.sqrt (n ^ 4 / D) ≤ Nat.sqrt (n ^ 4) := Nat.sqrt_le_sqrt (Nat.div_le_self _ _)
    _ = Nat.sqrt (n ^ 2 * n ^ 2) := by rw [← pow_add]
    _ = n ^ 2 := Nat.sqrt_eq _

/-- `2^{len + 1} ≤ 4(U + 1)` for the number `len` of binary digits of `U`. -/
private theorem two_pow_bitLen_le (U : ℕ) : 2 ^ (bitLen U + 1) ≤ 4 * (U + 1) := by
  rcases Nat.eq_zero_or_pos U with rfl | hU
  · simp [bitLen]
  · have hlen : 0 < bitLen U := Nat.size_pos.2 hU
    obtain ⟨b, hb⟩ : ∃ b, bitLen U = b + 1 := ⟨bitLen U - 1, by omega⟩
    have hpow : 2 ^ b ≤ U := Nat.lt_size.1 (by unfold bitLen at hb; omega)
    rw [hb, pow_succ, pow_succ]
    omega

/-- `2^⌈log₂ n⌉ ≤ 2(n + 1)`. -/
private theorem two_pow_clog_le (n : ℕ) : 2 ^ Nat.clog 2 n ≤ 2 * (n + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have := Nat.pow_clog_le_mul Nat.one_lt_two hn
    omega

/-- The number of binary digits of `U` is at most `U`. -/
private theorem polyBounded_bitLen : PolyBounded fun _ U => bitLen U :=
  PolyBounded.snd.of_le fun _ _ => Nat.size_le.2 Nat.lt_two_pow_self

/-- `2^{len + 1} ≤ 4(U + 1)` is polynomially bounded. -/
private theorem polyBounded_two_pow_bitLen : PolyBounded fun _ U => 2 ^ (bitLen U + 1) := by
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply Scale.SoftO.of_forall_le two_pow_bitLen_le
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply Light.PolyBounded.fst
                            | apply Light.PolyBounded.snd
                            | apply ThreeSumApsp.Scale.SoftO.log
                            | apply ThreeSumApsp.Scale.SoftO.sqrt
                            | apply Scale.SoftO.of_forall_le two_pow_bitLen_le
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply Light.PolyBounded.fst
                      | apply Light.PolyBounded.snd
                      | apply ThreeSumApsp.Scale.SoftO.log
                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                      | apply Scale.SoftO.of_forall_le two_pow_bitLen_le
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply Scale.SoftO.of_forall_le two_pow_bitLen_le
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- The size of the matrices of Strassen's recursion. -/
private theorem polyBounded_two_pow_clog : PolyBounded fun n _ => 2 ^ Nat.clog 2 n := by
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply Scale.SoftO.of_forall_le two_pow_clog_le
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply Light.PolyBounded.fst
                            | apply Light.PolyBounded.snd
                            | apply ThreeSumApsp.Scale.SoftO.log
                            | apply ThreeSumApsp.Scale.SoftO.sqrt
                            | apply Scale.SoftO.of_forall_le two_pow_clog_le
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply Light.PolyBounded.fst
                      | apply Light.PolyBounded.snd
                      | apply ThreeSumApsp.Scale.SoftO.log
                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                      | apply Scale.SoftO.of_forall_le two_pow_clog_le
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply Scale.SoftO.of_forall_le two_pow_clog_le
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- The depth of Strassen's recursion. -/
private theorem polyBounded_clog : PolyBounded fun n _ => Nat.clog 2 n :=
  polyBounded_two_pow_clog.of_le fun _ _ => Nat.lt_two_pow_self.le

/-- `(2^c)^⌈log₂ n⌉ = (2^⌈log₂ n⌉)^c`. -/
private theorem polyBounded_pow_clog (c : ℕ) : PolyBounded fun n _ => (2 ^ c) ^ Nat.clog 2 n :=
  (by first
      |
        ((apply ThreeSumApsp.Scale.SoftO.mono);
          (·
              repeat'
                with_reducible
                  first
                  | exact ThreeSumApsp.Scale.SoftO.const _
                  | apply Light.PolyBounded.fst
                  | apply Light.PolyBounded.snd
                  | apply ThreeSumApsp.Scale.SoftO.log
                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                  | apply polyBounded_two_pow_clog
                  | apply ThreeSumApsp.Scale.SoftO.add
                  | apply ThreeSumApsp.Scale.SoftO.mul
                  | apply ThreeSumApsp.Scale.SoftO.pow
                  | apply ThreeSumApsp.Scale.SoftO.max
                  | apply ThreeSumApsp.Scale.SoftO.sub
                  | apply ThreeSumApsp.Scale.SoftO.div);
          (·
              first
              | decide
              | exact isEmptyElim))
      |
        ((fail_if_success
              (fail_if_success
                  ((apply ThreeSumApsp.Scale.SoftO.mono);
                    (on_goal 1 =>
                        ((repeat'
                              with_reducible
                                first
                                | exact ThreeSumApsp.Scale.SoftO.const _
                                | apply Light.PolyBounded.fst
                                | apply Light.PolyBounded.snd
                                | apply ThreeSumApsp.Scale.SoftO.log
                                | apply ThreeSumApsp.Scale.SoftO.sqrt
                                | apply polyBounded_two_pow_clog
                                | apply ThreeSumApsp.Scale.SoftO.add
                                | apply ThreeSumApsp.Scale.SoftO.mul
                                | apply ThreeSumApsp.Scale.SoftO.pow
                                | apply ThreeSumApsp.Scale.SoftO.max
                                | apply ThreeSumApsp.Scale.SoftO.sub
                                | apply ThreeSumApsp.Scale.SoftO.div);
                          (done))))));
          (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
          (all_goals
              try
                ((apply ThreeSumApsp.Scale.SoftO.mono);
                  (·
                      repeat'
                        with_reducible
                          first
                          | exact ThreeSumApsp.Scale.SoftO.const _
                          | apply Light.PolyBounded.fst
                          | apply Light.PolyBounded.snd
                          | apply ThreeSumApsp.Scale.SoftO.log
                          | apply ThreeSumApsp.Scale.SoftO.sqrt
                          | apply polyBounded_two_pow_clog
                          | apply ThreeSumApsp.Scale.SoftO.add
                          | apply ThreeSumApsp.Scale.SoftO.mul
                          | apply ThreeSumApsp.Scale.SoftO.pow
                          | apply ThreeSumApsp.Scale.SoftO.max
                          | apply ThreeSumApsp.Scale.SoftO.sub
                          | apply ThreeSumApsp.Scale.SoftO.div);
                  (· decide))))
      |
        ((apply ThreeSumApsp.Scale.SoftO.mono);
          (·
              repeat'
                with_reducible
                  first
                  | exact ThreeSumApsp.Scale.SoftO.const _
                  | apply Light.PolyBounded.fst
                  | apply Light.PolyBounded.snd
                  | apply ThreeSumApsp.Scale.SoftO.log
                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                  | apply polyBounded_two_pow_clog
                  | apply ThreeSumApsp.Scale.SoftO.add
                  | apply ThreeSumApsp.Scale.SoftO.mul
                  | apply ThreeSumApsp.Scale.SoftO.pow
                  | apply ThreeSumApsp.Scale.SoftO.max
                  | apply ThreeSumApsp.Scale.SoftO.sub
                  | apply ThreeSumApsp.Scale.SoftO.div)) :
    PolyBounded fun n _ => (2 ^ Nat.clog 2 n) ^ c).of_le fun n _ => by
      rw [← pow_mul, ← pow_mul, mul_comm]

variable {D g : ℕ → ℕ}

/-- The number of query pairs of an instance. -/
private theorem polyBounded_queryCapNat : PolyBounded fun n _ => queryCapNat n (D n) := by
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply Scale.SoftO.of_forall_le₂ queryCapNat_le_sq
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply Light.PolyBounded.fst
                            | apply Light.PolyBounded.snd
                            | apply ThreeSumApsp.Scale.SoftO.log
                            | apply ThreeSumApsp.Scale.SoftO.sqrt
                            | apply Scale.SoftO.of_forall_le₂ queryCapNat_le_sq
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply Light.PolyBounded.fst
                      | apply Light.PolyBounded.snd
                      | apply ThreeSumApsp.Scale.SoftO.log
                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                      | apply Scale.SoftO.of_forall_le₂ queryCapNat_le_sq
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply Scale.SoftO.of_forall_le₂ queryCapNat_le_sq
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-! ## The numbers, the cells, and the solver -/

section parts

variable (hD : PolyBounded fun n _ => D n)
include hD

/-- The numbers that the host forms. -/
private theorem polyBounded_hostWord {a b : ℕ → ℕ} (ha : PolyBounded fun n _ => a n)
    (hb : PolyBounded fun n _ => b n) (hg : PolyBounded fun n _ => g n) :
    PolyBounded fun n U => hostWord (a n) (b n) n U (D n) (g n) := by
  have hring : PolyBounded fun n _ => 16 ^ Nat.clog 2 n := polyBounded_pow_clog 4
  unfold hostWord pieceSizeNat
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply ha
              | apply hb
              | apply hD
              | apply hg
              | apply polyBounded_two_pow_bitLen
              | apply hring
              | apply Scale.SoftO.ceilDiv
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply Light.PolyBounded.fst
                            | apply Light.PolyBounded.snd
                            | apply ThreeSumApsp.Scale.SoftO.log
                            | apply ThreeSumApsp.Scale.SoftO.sqrt
                            | apply ha
                            | apply hb
                            | apply hD
                            | apply hg
                            | apply polyBounded_two_pow_bitLen
                            | apply hring
                            | apply Scale.SoftO.ceilDiv
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply Light.PolyBounded.fst
                      | apply Light.PolyBounded.snd
                      | apply ThreeSumApsp.Scale.SoftO.log
                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                      | apply ha
                      | apply hb
                      | apply hD
                      | apply hg
                      | apply polyBounded_two_pow_bitLen
                      | apply hring
                      | apply Scale.SoftO.ceilDiv
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply ha
              | apply hb
              | apply hD
              | apply hg
              | apply polyBounded_two_pow_bitLen
              | apply hring
              | apply Scale.SoftO.ceilDiv
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- The cells of the arrays of the host. -/
private theorem polyBounded_hostLayout : PolyBounded fun n U => hostLayout n U (D n) := by
  unfold hostLayout
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply hD
              | apply polyBounded_bitLen
              | apply polyBounded_queryCapNat
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply Light.PolyBounded.fst
                            | apply Light.PolyBounded.snd
                            | apply ThreeSumApsp.Scale.SoftO.log
                            | apply ThreeSumApsp.Scale.SoftO.sqrt
                            | apply hD
                            | apply polyBounded_bitLen
                            | apply polyBounded_queryCapNat
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply Light.PolyBounded.fst
                      | apply Light.PolyBounded.snd
                      | apply ThreeSumApsp.Scale.SoftO.log
                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                      | apply hD
                      | apply polyBounded_bitLen
                      | apply polyBounded_queryCapNat
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply hD
              | apply polyBounded_bitLen
              | apply polyBounded_queryCapNat
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- The cells for the choice of the prime.  The scratch space of Strassen's recursion is at most
the size `4^K s` of a matrix, with `K = ⌈log₂ n⌉` and `s = ⌊√D⌋`. -/
private theorem polyBounded_chooseCells : PolyBounded fun n U => chooseCells n U (D n) := by
  have hmatrix : PolyBounded fun n _ => 4 ^ Nat.clog 2 n := polyBounded_pow_clog 2
  unfold chooseCells countCells
  first
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply hD
              | apply polyBounded_bitLen
              | apply polyBounded_two_pow_clog
              | apply polyBounded_clog
              | apply hmatrix
              | apply Scale.SoftO.of_forall_le₂ strScr_le
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div);
      (·
          first
          | decide
          | exact isEmptyElim))
  |
    ((fail_if_success
          (fail_if_success
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (on_goal 1 =>
                    ((repeat'
                          with_reducible
                            first
                            | exact ThreeSumApsp.Scale.SoftO.const _
                            | apply Light.PolyBounded.fst
                            | apply Light.PolyBounded.snd
                            | apply ThreeSumApsp.Scale.SoftO.log
                            | apply ThreeSumApsp.Scale.SoftO.sqrt
                            | apply hD
                            | apply polyBounded_bitLen
                            | apply polyBounded_two_pow_clog
                            | apply polyBounded_clog
                            | apply hmatrix
                            | apply Scale.SoftO.of_forall_le₂ strScr_le
                            | apply ThreeSumApsp.Scale.SoftO.add
                            | apply ThreeSumApsp.Scale.SoftO.mul
                            | apply ThreeSumApsp.Scale.SoftO.pow
                            | apply ThreeSumApsp.Scale.SoftO.max
                            | apply ThreeSumApsp.Scale.SoftO.sub
                            | apply ThreeSumApsp.Scale.SoftO.div);
                      (done))))));
      (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
      (all_goals
          try
            ((apply ThreeSumApsp.Scale.SoftO.mono);
              (·
                  repeat'
                    with_reducible
                      first
                      | exact ThreeSumApsp.Scale.SoftO.const _
                      | apply Light.PolyBounded.fst
                      | apply Light.PolyBounded.snd
                      | apply ThreeSumApsp.Scale.SoftO.log
                      | apply ThreeSumApsp.Scale.SoftO.sqrt
                      | apply hD
                      | apply polyBounded_bitLen
                      | apply polyBounded_two_pow_clog
                      | apply polyBounded_clog
                      | apply hmatrix
                      | apply Scale.SoftO.of_forall_le₂ strScr_le
                      | apply ThreeSumApsp.Scale.SoftO.add
                      | apply ThreeSumApsp.Scale.SoftO.mul
                      | apply ThreeSumApsp.Scale.SoftO.pow
                      | apply ThreeSumApsp.Scale.SoftO.max
                      | apply ThreeSumApsp.Scale.SoftO.sub
                      | apply ThreeSumApsp.Scale.SoftO.div);
              (· decide))))
  |
    ((apply ThreeSumApsp.Scale.SoftO.mono);
      (·
          repeat'
            with_reducible
              first
              | exact ThreeSumApsp.Scale.SoftO.const _
              | apply Light.PolyBounded.fst
              | apply Light.PolyBounded.snd
              | apply ThreeSumApsp.Scale.SoftO.log
              | apply ThreeSumApsp.Scale.SoftO.sqrt
              | apply hD
              | apply polyBounded_bitLen
              | apply polyBounded_two_pow_clog
              | apply polyBounded_clog
              | apply hmatrix
              | apply Scale.SoftO.of_forall_le₂ strScr_le
              | apply ThreeSumApsp.Scale.SoftO.add
              | apply ThreeSumApsp.Scale.SoftO.mul
              | apply ThreeSumApsp.Scale.SoftO.pow
              | apply ThreeSumApsp.Scale.SoftO.max
              | apply ThreeSumApsp.Scale.SoftO.sub
              | apply ThreeSumApsp.Scale.SoftO.div))

/-- A polynomially bounded function of the parameters `n`, `D`, `w` of an instance, at its largest
over the instances of the host, which have at most `⌊n²/√D⌋` query pairs. -/
private theorem polyBounded_sup {f : List ℕ → ℕ} {s k : ℕ} (hf : ∀ ps, f ps ≤ polyBound s k ps) :
    PolyBounded fun n _ => (Finset.range (queryCapNat n (D n) + 1)).sup fun w => f [n, D n, w] := by
  have hbound :
      PolyBounded fun n _ => 2 ^ s * ((n + 1) * ((D n + 1) * (queryCapNat n (D n) + 1))) ^ k := by
    first
    |
      ((apply ThreeSumApsp.Scale.SoftO.mono);
        (·
            repeat'
              with_reducible
                first
                | exact ThreeSumApsp.Scale.SoftO.const _
                | apply Light.PolyBounded.fst
                | apply Light.PolyBounded.snd
                | apply ThreeSumApsp.Scale.SoftO.log
                | apply ThreeSumApsp.Scale.SoftO.sqrt
                | apply hD
                | apply polyBounded_queryCapNat
                | apply ThreeSumApsp.Scale.SoftO.add
                | apply ThreeSumApsp.Scale.SoftO.mul
                | apply ThreeSumApsp.Scale.SoftO.pow
                | apply ThreeSumApsp.Scale.SoftO.max
                | apply ThreeSumApsp.Scale.SoftO.sub
                | apply ThreeSumApsp.Scale.SoftO.div);
        (·
            first
            | decide
            | exact isEmptyElim))
    |
      ((fail_if_success
            (fail_if_success
                ((apply ThreeSumApsp.Scale.SoftO.mono);
                  (on_goal 1 =>
                      ((repeat'
                            with_reducible
                              first
                              | exact ThreeSumApsp.Scale.SoftO.const _
                              | apply Light.PolyBounded.fst
                              | apply Light.PolyBounded.snd
                              | apply ThreeSumApsp.Scale.SoftO.log
                              | apply ThreeSumApsp.Scale.SoftO.sqrt
                              | apply hD
                              | apply polyBounded_queryCapNat
                              | apply ThreeSumApsp.Scale.SoftO.add
                              | apply ThreeSumApsp.Scale.SoftO.mul
                              | apply ThreeSumApsp.Scale.SoftO.pow
                              | apply ThreeSumApsp.Scale.SoftO.max
                              | apply ThreeSumApsp.Scale.SoftO.sub
                              | apply ThreeSumApsp.Scale.SoftO.div);
                        (done))))));
        (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
        (all_goals
            try
              ((apply ThreeSumApsp.Scale.SoftO.mono);
                (·
                    repeat'
                      with_reducible
                        first
                        | exact ThreeSumApsp.Scale.SoftO.const _
                        | apply Light.PolyBounded.fst
                        | apply Light.PolyBounded.snd
                        | apply ThreeSumApsp.Scale.SoftO.log
                        | apply ThreeSumApsp.Scale.SoftO.sqrt
                        | apply hD
                        | apply polyBounded_queryCapNat
                        | apply ThreeSumApsp.Scale.SoftO.add
                        | apply ThreeSumApsp.Scale.SoftO.mul
                        | apply ThreeSumApsp.Scale.SoftO.pow
                        | apply ThreeSumApsp.Scale.SoftO.max
                        | apply ThreeSumApsp.Scale.SoftO.sub
                        | apply ThreeSumApsp.Scale.SoftO.div);
                (· decide))))
    |
      ((apply ThreeSumApsp.Scale.SoftO.mono);
        (·
            repeat'
              with_reducible
                first
                | exact ThreeSumApsp.Scale.SoftO.const _
                | apply Light.PolyBounded.fst
                | apply Light.PolyBounded.snd
                | apply ThreeSumApsp.Scale.SoftO.log
                | apply ThreeSumApsp.Scale.SoftO.sqrt
                | apply hD
                | apply polyBounded_queryCapNat
                | apply ThreeSumApsp.Scale.SoftO.add
                | apply ThreeSumApsp.Scale.SoftO.mul
                | apply ThreeSumApsp.Scale.SoftO.pow
                | apply ThreeSumApsp.Scale.SoftO.max
                | apply ThreeSumApsp.Scale.SoftO.sub
                | apply ThreeSumApsp.Scale.SoftO.div))
  refine hbound.of_le fun n _ => Finset.sup_le fun w hw => (hf _).trans ?_
  have hw' : w ≤ queryCapNat n (D n) := Nat.lt_succ_iff.1 (Finset.mem_range.1 hw)
  simp only [polyBound, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  gcongr

end parts

end HostPoly

open HostPoly in
/-- **The need of the host stays polynomial**, if the parameters, the numbers that the parameter
procedures form, and the need of the solver are polynomially bounded. -/
theorem hostNeed_poly {Dfun Gfun wD wG : ℕ → ℕ} {need : List ℕ → Need}
    (hD : PolyBounded fun n _ => Dfun n) (hG : PolyBounded fun n _ => Gfun (Dfun n))
    (hwD : PolyBounded fun n _ => wD n) (hwG : PolyBounded fun n _ => wG (Dfun n))
    (h : PolyNeedN need) :
    PolyNeed (hostNeed Dfun Gfun wD wG need) := by
  obtain ⟨s, k, hle⟩ := h
  unfold hostNeed hostNeedAt supNeed
  (refine Light.PolyBounded.polyNeed ?_ ?_ ?_ <;> dsimp only <;>
      first
      |
        ((apply ThreeSumApsp.Scale.SoftO.mono);
          (·
              repeat'
                with_reducible
                  first
                  | exact ThreeSumApsp.Scale.SoftO.const _
                  | apply Light.PolyBounded.fst
                  | apply Light.PolyBounded.snd
                  | apply ThreeSumApsp.Scale.SoftO.log
                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                  | apply polyBounded_hostWord hD hwD hwG hG
                  | apply polyBounded_chooseCells hD
                  | apply polyBounded_hostLayout hD
                  | apply polyBounded_clog
                  | apply polyBounded_sup hD fun ps => (hle ps).1
                  | apply polyBounded_sup hD fun ps => (hle ps).2.1
                  | apply polyBounded_sup hD fun ps => (hle ps).2.2
                  | apply ThreeSumApsp.Scale.SoftO.add
                  | apply ThreeSumApsp.Scale.SoftO.mul
                  | apply ThreeSumApsp.Scale.SoftO.pow
                  | apply ThreeSumApsp.Scale.SoftO.max
                  | apply ThreeSumApsp.Scale.SoftO.sub
                  | apply ThreeSumApsp.Scale.SoftO.div);
          (·
              first
              | decide
              | exact isEmptyElim))
      |
        ((fail_if_success
              (fail_if_success
                  ((apply ThreeSumApsp.Scale.SoftO.mono);
                    (on_goal 1 =>
                        ((repeat'
                              with_reducible
                                first
                                | exact ThreeSumApsp.Scale.SoftO.const _
                                | apply Light.PolyBounded.fst
                                | apply Light.PolyBounded.snd
                                | apply ThreeSumApsp.Scale.SoftO.log
                                | apply ThreeSumApsp.Scale.SoftO.sqrt
                                | apply polyBounded_hostWord hD hwD hwG hG
                                | apply polyBounded_chooseCells hD
                                | apply polyBounded_hostLayout hD
                                | apply polyBounded_clog
                                | apply polyBounded_sup hD fun ps => (hle ps).1
                                | apply polyBounded_sup hD fun ps => (hle ps).2.1
                                | apply polyBounded_sup hD fun ps => (hle ps).2.2
                                | apply ThreeSumApsp.Scale.SoftO.add
                                | apply ThreeSumApsp.Scale.SoftO.mul
                                | apply ThreeSumApsp.Scale.SoftO.pow
                                | apply ThreeSumApsp.Scale.SoftO.max
                                | apply ThreeSumApsp.Scale.SoftO.sub
                                | apply ThreeSumApsp.Scale.SoftO.div);
                          (done))))));
          (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le);
          (all_goals
              try
                ((apply ThreeSumApsp.Scale.SoftO.mono);
                  (·
                      repeat'
                        with_reducible
                          first
                          | exact ThreeSumApsp.Scale.SoftO.const _
                          | apply Light.PolyBounded.fst
                          | apply Light.PolyBounded.snd
                          | apply ThreeSumApsp.Scale.SoftO.log
                          | apply ThreeSumApsp.Scale.SoftO.sqrt
                          | apply polyBounded_hostWord hD hwD hwG hG
                          | apply polyBounded_chooseCells hD
                          | apply polyBounded_hostLayout hD
                          | apply polyBounded_clog
                          | apply polyBounded_sup hD fun ps => (hle ps).1
                          | apply polyBounded_sup hD fun ps => (hle ps).2.1
                          | apply polyBounded_sup hD fun ps => (hle ps).2.2
                          | apply ThreeSumApsp.Scale.SoftO.add
                          | apply ThreeSumApsp.Scale.SoftO.mul
                          | apply ThreeSumApsp.Scale.SoftO.pow
                          | apply ThreeSumApsp.Scale.SoftO.max
                          | apply ThreeSumApsp.Scale.SoftO.sub
                          | apply ThreeSumApsp.Scale.SoftO.div);
                  (· decide))))
      |
        ((apply ThreeSumApsp.Scale.SoftO.mono);
          (·
              repeat'
                with_reducible
                  first
                  | exact ThreeSumApsp.Scale.SoftO.const _
                  | apply Light.PolyBounded.fst
                  | apply Light.PolyBounded.snd
                  | apply ThreeSumApsp.Scale.SoftO.log
                  | apply ThreeSumApsp.Scale.SoftO.sqrt
                  | apply polyBounded_hostWord hD hwD hwG hG
                  | apply polyBounded_chooseCells hD
                  | apply polyBounded_hostLayout hD
                  | apply polyBounded_clog
                  | apply polyBounded_sup hD fun ps => (hle ps).1
                  | apply polyBounded_sup hD fun ps => (hle ps).2.1
                  | apply polyBounded_sup hD fun ps => (hle ps).2.2
                  | apply ThreeSumApsp.Scale.SoftO.add
                  | apply ThreeSumApsp.Scale.SoftO.mul
                  | apply ThreeSumApsp.Scale.SoftO.pow
                  | apply ThreeSumApsp.Scale.SoftO.max
                  | apply ThreeSumApsp.Scale.SoftO.sub
                  | apply ThreeSumApsp.Scale.SoftO.div)))

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

/-- **The context of the top procedure**, in the assembled program with anything appended to
it. -/
theorem et17Ctx_assembled (hsol : SolvesN lopDetectTask P₀ pS Tn need)
    (hD : ∀ R, ParamProc (P₀ ++ R) pD Dfun tD wD) (hG : ∀ R, ParamProc (P₀ ++ R) pG Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n) (R : Program) :
    Et17Ctx P₀ (et17Procs pS pD pG P₀.length ++ R) (et17NumsAt pS pD pG P₀.length) Tn need Dfun Gfun
      tD tG wD wG := by
  -- Procedure number `i` of the list.
  have L : ∀ {i : ℕ} {body : Stmt}, (et17Procs pS pD pG P₀.length)[i]? = some body →
      (P₀ ++ (et17Procs pS pD pG P₀.length ++ R))[P₀.length + i]? = some body :=
    fun h => getElem?_append_append R h
  exact
    { loop := ⟨hsol, L rfl, L rfl, L rfl, L rfl⟩
      hLoop := L rfl
      hSqrt := L (i := 0) rfl
      hBrute := L rfl
      hChoose := L rfl
      ch := ⟨L rfl, L rfl, L rfl,
        ⟨L rfl, L rfl, L rfl, L rfl, L rfl,
          L rfl, L rfl,
          ⟨L rfl, L rfl, L rfl, L rfl, L rfl⟩⟩,
        ⟨L (i := 0) rfl, L rfl⟩⟩
      hCap := L rfl
      hCeil := L rfl
      hBitLen := L rfl
      hDbl := L rfl
      hResid := L rfl
      hResidues := L rfl
      hClasses := L rfl
      hChunks := L rfl
      dProc := hD _
      gProc := hG _
      D_pos := hpos }

/-- **The host of Theorem 17 as a solver of Exact Triangle**: from a solver of Lop-AE-SparseTri and
two procedures that compute the parameters, in one program `P₀`, the appended procedures make a
solver of Exact Triangle with the time `hostTime` and the need `hostNeed`. -/
theorem et17_solves (hsol : SolvesN lopDetectTask P₀ pS Tn need)
    (hD : ∀ R, ParamProc (P₀ ++ R) pD Dfun tD wD) (hG : ∀ R, ParamProc (P₀ ++ R) pG Gfun tG wG)
    (hpos : ∀ n, 1 ≤ n → 1 ≤ Dfun n) :
    Solves etTask (P₀ ++ et17Procs pS pD pG P₀.length) (P₀.length + 27)
      (hostTime Dfun Gfun tD tG Tn) (hostNeed Dfun Gfun wD wG need) := by
  refine ⟨et17Body (et17NumsAt pS pD pG P₀.length), ?_, fun R lim d x μ fr hpre hok => ?_⟩
  · have htop := getElem?_append_append (P₀ := P₀) (B := et17Procs pS pD pG P₀.length) [] (i := 27)
      rfl
    rwa [List.append_nil] at htop
  · rw [List.append_assoc]
    exact et17_spec (et17Ctx_assembled hsol hD hG hpos R) x μ fr hpre hok

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
















/-- **From a host to the claim.**  `time` and `need` are the host's time and need as functions of
those of the solver.  A program has a natural number `U` as the bound on the weights and the claim a
real number `u`; the time for `u` is the largest time for a `U ≤ u`. -/
theorem claim17_of_host (MM : ℕ → ℝ) (D g : ℕ → ℕ) (time : (List ℕ → ℕ) → ℕ → ℕ → ℕ)
    (need : (List ℕ → Need) → ℕ → ℕ → Need)
    (host : ∀ (Q : Program) (pS : ℕ) (Tn : List ℕ → ℕ) (r : List ℕ → Need), PolyNeedN r →
      SolvesN lopDetectTask Q pS Tn r →
      ∃ (R : Program) (p' : ℕ), Solves etTask (Q ++ R) p' (time Tn) (need r) ∧ PolyNeed (need r))
    (bound : ObeysBound17 MM D g time) :
    Claim.Theorem_17 lightModel MM D g := by
  obtain ⟨C, hC, bound⟩ := bound
  refine ⟨C, hC, fun T hT => ?_⟩
  obtain ⟨Q, pS, Tn, r, hpoly, hsolves, hle⟩ := hT
  obtain ⟨R, p', hs, hp⟩ := host Q pS Tn r hpoly hsolves
  exact ⟨timeUpTo (time Tn), hs.solvedIn hp, fun n κ u h16 hDn hg1 hg hκ hu =>
    timeUpTo_le fun U hU =>
      bound Tn T hle n U κ h16 hDn hg1 hg hκ (hU.trans (max_le hu (by positivity)))⟩

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

/-- `D ≥ 1`, as a natural number. -/
theorem one_le_D_nat : 1 ≤ θ.D := (by norm_num : 1 ≤ 16).trans h.hD16










































end CostParams.Hyp

/-! ## Numbers of steps up to a constant -/






namespace Steps

variable {t t₁ t₂ : CostParams → ℕ} {B B₁ B₂ : CostParams → ℝ}





/-- A larger bound. -/
theorem mono_right (h : Steps t B₁) (hle : ∀ θ, θ.Hyp → B₁ θ ≤ B₂ θ) : Steps t B₂ :=
  Dominated.mono_right h hle



















end Steps

/-! ## Monomials -/












theorem mon_eq (a b c : ℕ) (θ : CostParams) :
    mon a b c θ = (θ.n : ℝ) ^ a * Real.sqrt θ.D ^ b * (θ.κ * Real.log θ.n) ^ c := by
  simp [Scale.mon, costScale, Scale.ofBases, Fin.prod_univ_three]




/-- A bound by a monomial, as a bound up to a constant. -/
theorem steps_of_softO {t : CostParams → ℕ} {e : Fin 3 → ℕ} (h : costScale.SoftO t e) :
    Steps t (costScale.mon e) :=
  h.dominated fun _ _ => rfl

/-! ## The basic quantities -/

/-- The number of vertices per part. -/
theorem steps_n : StepsMon (fun θ => θ.n) 1 0 0 :=
  (Scale.SoftO.of_le_base 0 fun _ _ => le_rfl).mono (by decide)





/-- `D = (√D)²`. -/
theorem steps_D : StepsMon (fun θ => θ.D) 0 2 0 :=
  .of_dominated <| .of_le fun θ _ => by
    simp only [mon_eq, pow_zero, mul_one, one_mul, Real.sq_sqrt θ.D.cast_nonneg, le_refl]

















































/-! ## The routines -/














































































/-! ## The three terms of the bound dominate the monomials -/






























/-- `n² (√D)² ≤ n² D g`. -/
private theorem mon_le_termBuild {θ : CostParams} (hθ : θ.Hyp) :
    mon 2 2 0 θ ≤ termBuild θ.n θ.D θ.g := by
  rw [termBuild, mon_eq, pow_zero, mul_one, Real.sq_sqrt θ.D.cast_nonneg]
  exact le_mul_of_one_le_right (by positivity) hθ.one_le_g





/-- The first term is not negative. -/
private theorem termScans_nonneg {θ : CostParams} (hθ : θ.Hyp) : 0 ≤ termScans θ.n θ.g θ.κ := by
  have hκ : 0 ≤ θ.κ := zero_le_one.trans hθ.hκ
  unfold termScans
  positivity

/-- The second term is not negative. -/
private theorem termPrime_nonneg (θ : CostParams) : 0 ≤ termPrime strassen θ.n θ.D := by
  unfold termPrime strassen
  positivity





















/-- The third term is at most the sum. -/
theorem termBuild_le_budget {θ : CostParams} (hθ : θ.Hyp) :
    termBuild θ.n θ.D θ.g ≤ budget θ := by
  unfold budget
  linarith [termScans_nonneg hθ, termPrime_nonneg θ]

section within

variable {t : CostParams → ℕ} {e : Fin 3 → ℕ}













/-- Within the third term, `n² D g`. -/
theorem _root_.ThreeSumApsp.Scale.SoftO.withinBuild (h : costScale.SoftO t e)
    (he : ∀ i, e i ≤ ![2, 2, 0] i := by decide) : Steps t budget :=
  (steps_of_softO (h.mono he)).mono_right fun _ hθ =>
    (mon_le_termBuild hθ).trans (termBuild_le_budget hθ)

end within

namespace Steps

variable {t₁ t₂ m : CostParams → ℕ} {B : CostParams → ℝ}






end Steps

/-! ## The choice of the prime -/







































































end Light.Sec3

end
end

section
-- Source module: ThreeSumApsp.AllEdges.RatParams
@[expose] public section

namespace ThreeSumApsp

open Spec

/-- The real power of a natural power. -/
private theorem rpow_pow_inv (n a b : ℕ) :
    (((n ^ a : ℕ) : ℝ)) ^ ((b : ℝ)⁻¹) = (n : ℝ) ^ ((a : ℝ) / b) := by
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n), div_eq_mul_inv]

/-- `paramDr a b n = ⌊n^{a/b}⌋`. -/
theorem paramDr_eq_floor {a b : ℕ} (hb : 1 ≤ b) (n : ℕ) :
    paramDr a b n = ⌊(n : ℝ) ^ ((a : ℝ) / b)⌋₊ := by
  rw [← rpow_pow_inv, floor_rpow_inv (by omega)]
  rfl

/-- `⌊n^{a/b}⌋ ≤ n^{a/b}`. -/
theorem paramDr_le_rpow {a b : ℕ} (hb : 1 ≤ b) (n : ℕ) :
    (paramDr a b n : ℝ) ≤ (n : ℝ) ^ ((a : ℝ) / b) := by
  rw [paramDr_eq_floor hb]
  exact Nat.floor_le (by positivity)

/-- `n^{a/b} < ⌊n^{a/b}⌋ + 1`. -/
theorem rpow_lt_paramDr_add_one {a b : ℕ} (hb : 1 ≤ b) (n : ℕ) :
    (n : ℝ) ^ ((a : ℝ) / b) < paramDr a b n + 1 := by
  rw [paramDr_eq_floor hb]
  exact Nat.lt_floor_add_one _

/-- `paramGr c e D = ⌈D^{c/e}⌉` for `D ≥ 1`. -/
theorem paramGr_eq_ceil {c e : ℕ} (he : 1 ≤ e) {D : ℕ} (hD : 1 ≤ D) :
    paramGr c e D = ⌈(D : ℝ) ^ ((c : ℝ) / e)⌉₊ := by
  rw [← rpow_pow_inv, ceil_rpow_inv (by omega) (Nat.one_le_pow _ _ hD)]
  rfl

/-- `D^{c/e} ≤ ⌈D^{c/e}⌉`. -/
theorem rpow_le_paramGr {c e : ℕ} (he : 1 ≤ e) {D : ℕ} (hD : 1 ≤ D) :
    (D : ℝ) ^ ((c : ℝ) / e) ≤ paramGr c e D := by
  rw [paramGr_eq_ceil he hD]
  exact Nat.le_ceil _

/-- `⌈D^{c/e}⌉ < D^{c/e} + 1`. -/
theorem paramGr_lt_rpow_add_one {c e : ℕ} (he : 1 ≤ e) {D : ℕ} (hD : 1 ≤ D) :
    (paramGr c e D : ℝ) < (D : ℝ) ^ ((c : ℝ) / e) + 1 := by
  rw [paramGr_eq_ceil he hD]
  exact Nat.ceil_lt_add_one (by positivity)

/-- `⌊n^{a/b}⌋ ≤ n` for `a ≤ b`. -/
theorem paramDr_le {a b : ℕ} (hb : 1 ≤ b) (hab : a ≤ b) {n : ℕ} (hn : 1 ≤ n) :
    paramDr a b n ≤ n := by
  have h := rootFloor_pow_le (e := b) (by omega) (n ^ a)
  have h' : rootFloor b (n ^ a) ^ b ≤ n ^ b := h.trans (Nat.pow_le_pow_right hn hab)
  exact (Nat.pow_le_pow_iff_left (by omega)).1 h'

/-- `⌊n^{a/b}⌋ ≥ 1` for `n ≥ 1`. -/
theorem one_le_paramDr {a b : ℕ} (hb : 1 ≤ b) {n : ℕ} (hn : 1 ≤ n) : 1 ≤ paramDr a b n :=
  le_rootFloor (by omega) (by rw [one_pow]; exact Nat.one_le_pow _ _ hn)

/-- `⌈D^{c/e}⌉ ≥ 1`. -/
theorem one_le_paramGr (c e D : ℕ) : 1 ≤ paramGr c e D := Nat.succ_le_succ (Nat.zero_le _)

/-- `⌈D^{c/e}⌉ ≤ D` for `c ≤ e`. -/
theorem paramGr_le {c e : ℕ} (he : 1 ≤ e) (hce : c ≤ e) {D : ℕ} (hD : 1 ≤ D) :
    paramGr c e D ≤ D :=
  rootCeil_le (by omega) (Nat.one_le_pow _ _ hD) (Nat.pow_le_pow_right hD hce)

end ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-- **dr** returns `⌊n^{a/b}⌋`, for n ≥ 1. -/
theorem dr_spec {μ : ℕ → ℤ} {a b pRoot pPow n : ℕ} (hR : P[pRoot]? = some (rootCeilBody pPow))
    (hP : P[pPow]? = some powLtBody) (hb : 1 ≤ b) (hn : 1 ≤ n)
    (hword : ((wDr a b n : ℕ) : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth) :
    Ends lim P d (drBody a b pRoot) ⟨Light.frame [n], μ⟩ (tDr a b n) fun σ' =>
      σ'.loc 0 = (paramDr a b n : ℕ) ∧ σ'.mem = μ := by
  have hroot : rootCeil b (n ^ a + 1) = paramDr a b n + 1 := rootCeil_succ (by omega) _
  have h1 : n ^ a + 1 ≤ (n ^ a + 1) * (paramDr a b n + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hfits : ((n ^ a + 1 + a + b + 1 : ℕ) : ℤ) ≤ lim.word :=
    le_trans (by unfold wDr; exact_mod_cast (by omega)) hword
  simp only [Nat.cast_add, Nat.cast_one] at hfits
  have hpow0 : (0 : ℤ) ≤ ((n ^ a : ℕ) : ℤ) := Int.natCast_nonneg _
  have hcast : ((n : ℤ)) ^ a = ((n ^ a : ℕ) : ℤ) := by push_cast; rfl
  have hP1 : ((paramDr a b n + 1 : ℕ) : ℤ) ≤ lim.word :=
    le_trans (by unfold wDr; exact_mod_cast (by nlinarith)) hword
  push_cast at hP1
  unfold tDr
  -- cnt := 0; prod := 1
  (focus
     ((first
         | refine Light.Ends.seqSelf ?_
         | refine Light.Ends.skipLast ?_);
       (repeat
           with_unfolding_none
             first
             | refine Light.Ends.seqAssoc ?_
             | refine Light.Ends.skipThen ?_))
     (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_)
     (on_goal -1 =>
         first
         | ( (simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost, List.map_cons,
                 List.map_nil, List.sum_cons, List.sum_nil, ])
             (first
               | omega
               | ((ring_nf); (omega))))
         | omega
         |
           (simp [] <;>
               first
               | omega
               | ((ring_nf); (omega))))
     (on_goal -1 =>
         ( (try have := Light.Std.space_le (by assumption))
           (try have := Light.Std.const_le (by assumption))
           (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
     (try with_unfolding_none refine Light.Ends.skip ?_))
  (focus
     ((first
         | refine Light.Ends.seqSelf ?_
         | refine Light.Ends.skipLast ?_);
       (repeat
           with_unfolding_none
             first
             | refine Light.Ends.seqAssoc ?_
             | refine Light.Ends.skipThen ?_))
     (refine
         Light.Ends.setToThen
           (1 : ℕ)
             -- while cnt < a: prod := prod * n; cnt := cnt + 1.  Before round i, prod = n^i.
             
           ?_ ?_ ?_)
     (on_goal -1 =>
         first
         | ( (simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost, List.map_cons,
                 List.map_nil, List.sum_cons, List.sum_nil, ])
             (first
               | omega
               | ((ring_nf); (omega))))
         | omega
         |
           (simp [] <;>
               first
               | omega
               | ((ring_nf); (omega))))
     (on_goal -1 =>
         ( (try have := Light.Std.space_le (by assumption))
           (try have := Light.Std.const_le (by assumption))
           (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
     (try with_unfolding_none refine Light.Ends.skip ?_))
  -- while cnt < a: prod := prod * n; cnt := cnt + 1.  Before round i, prod = n^i.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨Light.frame [n, i, (n ^ i : ℕ)], μ⟩) a (by simp)
    ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hle : ((n ^ (i + 1) : ℕ) : ℤ) ≤ ((n ^ a : ℕ) : ℤ) := by
      exact_mod_cast Nat.pow_le_pow_right hn hi
    have hmul : ((n ^ i : ℕ) : ℤ) * n = ((n ^ (i + 1) : ℕ) : ℤ) := by push_cast; ring
    have hmul0 : (0 : ℤ) ≤ ((n ^ (i + 1) : ℕ) : ℤ) := Int.natCast_nonneg _
    generalize ((n ^ (i + 1) : ℕ) : ℤ) = q' at hle hmul hmul0
    generalize ((n ^ i : ℕ) : ℤ) = q at hmul
    exact ⟨by (( (try have := Light.Std.space_le (by assumption))
                 (try have := Light.Std.const_le (by assumption))
                 (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))), by (( (try have := Light.Std.space_le (by assumption))
                                                                                   (try have := Light.Std.const_le (by assumption))
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))), by (( (try have := Light.Std.space_le (by assumption))
                                                                                                                                                     (try have := Light.Std.const_le (by assumption))
                                                                                                                                                     (simp [Light.Limits.Addr, abs_le, -abs_mul, hmul] <;> omega))),
      by simp [update_frame_setLocal, hmul]⟩
  case done =>
    rintro _ rfl
    refine ⟨by (( (try have := Light.Std.space_le (by assumption))
                  (try have := Light.Std.const_le (by assumption))
                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))), by (( (try have := Light.Std.space_le (by assumption))
                                                                                    (try have := Light.Std.const_le (by assumption))
                                                                                    (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))), ?_⟩
    -- root := rootCeil(b, n^a + 1)
    refine Ends.callToThen (rootCeil_meets (e := b) (t := n ^ a + 1) hR hP (by omega) (by omega)
      (by rw [hroot]; exact le_trans (by unfold wDr; exact_mod_cast (by omega)) hword)
      (by omega)) ?_ (hT := by simp [tRootCeil, hroot]; omega)
    rintro _ μ' ⟨rfl, hμ⟩
    -- return root - 1
    rw [hroot, hμ]
    exact Ends.setTo (paramDr a b n) (by simp) (hT := by simp [tRootCeil, hroot]; omega)

/-- **gr** returns `⌈D^{c/e}⌉`, for D ≥ 1. -/
theorem gr_spec {μ : ℕ → ℤ} {c e pRoot pPow D : ℕ} (hR : P[pRoot]? = some (rootCeilBody pPow))
    (hP : P[pPow]? = some powLtBody) (he : 1 ≤ e) (hD : 1 ≤ D)
    (hword : ((wGr c e D : ℕ) : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth) :
    Ends lim P d (grBody c e pRoot) ⟨Light.frame [D], μ⟩ (tGr c e D) fun σ' =>
      σ'.loc 0 = (paramGr c e D : ℕ) ∧ σ'.mem = μ := by
  have hpos : 1 ≤ paramGr c e D := one_le_paramGr c e D
  have h1 : D ^ c ≤ D ^ c * paramGr c e D := Nat.le_mul_of_pos_right _ hpos
  have hfits : ((D ^ c + c + e + 1 : ℕ) : ℤ) ≤ lim.word := le_trans
    (by unfold wGr; exact_mod_cast (by omega)) hword
  simp only [Nat.cast_add, Nat.cast_one] at hfits
  have hpow0 : (0 : ℤ) ≤ ((D ^ c : ℕ) : ℤ) := Int.natCast_nonneg _
  unfold tGr
  -- cnt := 0; prod := 1
  (focus
     ((first
         | refine Light.Ends.seqSelf ?_
         | refine Light.Ends.skipLast ?_);
       (repeat
           with_unfolding_none
             first
             | refine Light.Ends.seqAssoc ?_
             | refine Light.Ends.skipThen ?_))
     (refine Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_)
     (on_goal -1 =>
         first
         | ( (simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost, List.map_cons,
                 List.map_nil, List.sum_cons, List.sum_nil, ])
             (first
               | omega
               | ((ring_nf); (omega))))
         | omega
         |
           (simp [] <;>
               first
               | omega
               | ((ring_nf); (omega))))
     (on_goal -1 =>
         ( (try have := Light.Std.space_le (by assumption))
           (try have := Light.Std.const_le (by assumption))
           (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
     (try with_unfolding_none refine Light.Ends.skip ?_))
  (focus
     ((first
         | refine Light.Ends.seqSelf ?_
         | refine Light.Ends.skipLast ?_);
       (repeat
           with_unfolding_none
             first
             | refine Light.Ends.seqAssoc ?_
             | refine Light.Ends.skipThen ?_))
     (refine
         Light.Ends.setToThen
           (1 : ℕ)
             -- while cnt < c: prod := prod * D; cnt := cnt + 1.  Before round i, prod = D^i.
             
           ?_ ?_ ?_)
     (on_goal -1 =>
         first
         | ( (simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost, List.map_cons,
                 List.map_nil, List.sum_cons, List.sum_nil, ])
             (first
               | omega
               | ((ring_nf); (omega))))
         | omega
         |
           (simp [] <;>
               first
               | omega
               | ((ring_nf); (omega))))
     (on_goal -1 =>
         ( (try have := Light.Std.space_le (by assumption))
           (try have := Light.Std.const_le (by assumption))
           (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
     (try with_unfolding_none refine Light.Ends.skip ?_))
  -- while cnt < c: prod := prod * D; cnt := cnt + 1.  Before round i, prod = D^i.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨Light.frame [D, i, (D ^ i : ℕ)], μ⟩) c (by simp)
    ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hle : ((D ^ (i + 1) : ℕ) : ℤ) ≤ ((D ^ c : ℕ) : ℤ) := by
      exact_mod_cast Nat.pow_le_pow_right hD hi
    have hmul : ((D ^ i : ℕ) : ℤ) * D = ((D ^ (i + 1) : ℕ) : ℤ) := by push_cast; ring
    have hmul0 : (0 : ℤ) ≤ ((D ^ (i + 1) : ℕ) : ℤ) := Int.natCast_nonneg _
    generalize ((D ^ (i + 1) : ℕ) : ℤ) = q' at hle hmul hmul0
    generalize ((D ^ i : ℕ) : ℤ) = q at hmul
    exact ⟨by (( (try have := Light.Std.space_le (by assumption))
                 (try have := Light.Std.const_le (by assumption))
                 (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))), by (( (try have := Light.Std.space_le (by assumption))
                                                                                   (try have := Light.Std.const_le (by assumption))
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))), by (( (try have := Light.Std.space_le (by assumption))
                                                                                                                                                     (try have := Light.Std.const_le (by assumption))
                                                                                                                                                     (simp [Light.Limits.Addr, abs_le, -abs_mul, hmul] <;> omega))),
      by simp [update_frame_setLocal, hmul]⟩
  case done =>
    rintro _ rfl
    -- return rootCeil(e, prod)
    exact ⟨by (( (try have := Light.Std.space_le (by assumption))
                 (try have := Light.Std.const_le (by assumption))
                 (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))), by (( (try have := Light.Std.space_le (by assumption))
                                                                                   (try have := Light.Std.const_le (by assumption))
                                                                                   (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega))),
      Ends.callTo (rootCeil_meets (e := e) (t := D ^ c) hR hP (by omega)
        (Nat.one_le_pow _ _ hD) (le_trans (by
          unfold wGr
          exact_mod_cast (show D ^ c * rootCeil e (D ^ c) + e + 1
            ≤ D ^ c * paramGr c e D + c + e + 1 by unfold paramGr; omega)) hword)
        (by omega)) (fun r μ' h => by simpa [paramGr] using h)
        (hT := by simp [tRootCeil, paramGr]; omega)⟩

end Light.Sec3
end
end

section
-- Source module: ThreeSumApsp.AllEdges.MidClaim
@[expose] public section

namespace ThreeSumApsp

namespace Claim

end Claim

end ThreeSumApsp
end

@[expose] public section
namespace Light.Sec3
open ThreeSumApsp ThreeSumApsp.Spec

section params

variable (a b c e : ℕ)

private theorem ratParamProcs_get (Q R : Program) {i : ℕ} {body : Stmt}
    (h : (ratParamProcs a b c e Q.length)[i]? = some body) :
    (Q ++ ratParamProcs a b c e Q.length ++ R)[Q.length + i]? = some body := by
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact getElem?_append_of_eq_some h R

variable {a b c e}

/-- dr is a parameter procedure. -/
theorem paramProc_dr (hb : 1 ≤ b) (Q R : Program) :
    ParamProc (Q ++ ratParamProcs a b c e Q.length ++ R) (Q.length + 2) (paramDr a b) (tDr a b)
      (wDr a b) := by
  intro lim d x μ hx _ hw hd
  exact ⟨_, ratParamProcs_get a b c e Q R (i := 2) rfl,
    dr_spec (ratParamProcs_get a b c e Q R (i := 1) rfl)
      (ratParamProcs_get a b c e Q R (i := 0) rfl) hb hx hw (by omega)⟩

/-- gr is a parameter procedure. -/
theorem paramProc_gr (he : 1 ≤ e) (Q R : Program) :
    ParamProc (Q ++ ratParamProcs a b c e Q.length ++ R) (Q.length + 3) (paramGr c e) (tGr c e)
      (wGr c e) := by
  intro lim d x μ hx _ hw hd
  exact ⟨_, ratParamProcs_get a b c e Q R (i := 3) rfl,
    gr_spec (ratParamProcs_get a b c e Q R (i := 1) rfl)
      (ratParamProcs_get a b c e Q R (i := 0) rfl) he hx hw (by omega)⟩

/-- `⌊n^{a/b}⌋ ≤ n + 1`. -/
private theorem paramDr_le_succ (hb : 1 ≤ b) (hab : a ≤ b) (n : ℕ) : paramDr a b n ≤ n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact (Nat.findGreatest_le _).trans (by rcases Nat.eq_zero_or_pos a with rfl | ha <;> simp [*])
  · exact (paramDr_le hb hab hn).trans (Nat.le_succ n)

theorem polyBounded_paramDr (hb : 1 ≤ b) (hab : a ≤ b) : PolyBounded fun n _ => paramDr a b n :=
  (by (first
       | ( (apply ThreeSumApsp.Scale.SoftO.mono)
           (·
               repeat'
                 with_reducible
                   first
                   | exact ThreeSumApsp.Scale.SoftO.const _
                   | apply Light.PolyBounded.fst
                   | apply Light.PolyBounded.snd
                   | apply ThreeSumApsp.Scale.SoftO.log
                   | apply ThreeSumApsp.Scale.SoftO.sqrt
                   | apply PolyBounded.fst
                   | apply ThreeSumApsp.Scale.SoftO.add
                   | apply ThreeSumApsp.Scale.SoftO.mul
                   | apply ThreeSumApsp.Scale.SoftO.pow
                   | apply ThreeSumApsp.Scale.SoftO.max
                   | apply ThreeSumApsp.Scale.SoftO.sub
                   | apply ThreeSumApsp.Scale.SoftO.div)
           (·
               first
               | decide
               | exact isEmptyElim))
       | ( (fail_if_success
               (fail_if_success
                   ( (apply ThreeSumApsp.Scale.SoftO.mono)
                     (on_goal 1 =>
                         ((repeat'
                               with_reducible
                                 first
                                 | exact ThreeSumApsp.Scale.SoftO.const _
                                 | apply Light.PolyBounded.fst
                                 | apply Light.PolyBounded.snd
                                 | apply ThreeSumApsp.Scale.SoftO.log
                                 | apply ThreeSumApsp.Scale.SoftO.sqrt
                                 | apply PolyBounded.fst
                                 | apply ThreeSumApsp.Scale.SoftO.add
                                 | apply ThreeSumApsp.Scale.SoftO.mul
                                 | apply ThreeSumApsp.Scale.SoftO.pow
                                 | apply ThreeSumApsp.Scale.SoftO.max
                                 | apply ThreeSumApsp.Scale.SoftO.sub
                                 | apply ThreeSumApsp.Scale.SoftO.div);
                           (done))))))
           (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le)
           (all_goals
               try (
                   (apply ThreeSumApsp.Scale.SoftO.mono)
                   (·
                       repeat'
                         with_reducible
                           first
                           | exact ThreeSumApsp.Scale.SoftO.const _
                           | apply Light.PolyBounded.fst
                           | apply Light.PolyBounded.snd
                           | apply ThreeSumApsp.Scale.SoftO.log
                           | apply ThreeSumApsp.Scale.SoftO.sqrt
                           | apply PolyBounded.fst
                           | apply ThreeSumApsp.Scale.SoftO.add
                           | apply ThreeSumApsp.Scale.SoftO.mul
                           | apply ThreeSumApsp.Scale.SoftO.pow
                           | apply ThreeSumApsp.Scale.SoftO.max
                           | apply ThreeSumApsp.Scale.SoftO.sub
                           | apply ThreeSumApsp.Scale.SoftO.div)
                   (· decide))))
       | ( (apply ThreeSumApsp.Scale.SoftO.mono)
           (·
               repeat'
                 with_reducible
                   first
                   | exact ThreeSumApsp.Scale.SoftO.const _
                   | apply Light.PolyBounded.fst
                   | apply Light.PolyBounded.snd
                   | apply ThreeSumApsp.Scale.SoftO.log
                   | apply ThreeSumApsp.Scale.SoftO.sqrt
                   | apply PolyBounded.fst
                   | apply ThreeSumApsp.Scale.SoftO.add
                   | apply ThreeSumApsp.Scale.SoftO.mul
                   | apply ThreeSumApsp.Scale.SoftO.pow
                   | apply ThreeSumApsp.Scale.SoftO.max
                   | apply ThreeSumApsp.Scale.SoftO.sub
                   | apply ThreeSumApsp.Scale.SoftO.div))) : PolyBounded fun n _ => n + 1).of_le fun n _ =>
    paramDr_le_succ hb hab n

/-- `⌈D^{c/e}⌉ ≤ D^c + 1`. -/
private theorem paramGr_le_succ (D : ℕ) : paramGr c e D ≤ D ^ c + 1 :=
  Nat.succ_le_succ (Nat.findGreatest_le _)

theorem polyBounded_paramGr {D : ℕ → ℕ} (hD : PolyBounded fun n _ => D n) :
    PolyBounded fun n _ => paramGr c e (D n) :=
  (by (first
       | ( (apply ThreeSumApsp.Scale.SoftO.mono)
           (·
               repeat'
                 with_reducible
                   first
                   | exact ThreeSumApsp.Scale.SoftO.const _
                   | apply Light.PolyBounded.fst
                   | apply Light.PolyBounded.snd
                   | apply ThreeSumApsp.Scale.SoftO.log
                   | apply ThreeSumApsp.Scale.SoftO.sqrt
                   | apply hD
                   | apply ThreeSumApsp.Scale.SoftO.add
                   | apply ThreeSumApsp.Scale.SoftO.mul
                   | apply ThreeSumApsp.Scale.SoftO.pow
                   | apply ThreeSumApsp.Scale.SoftO.max
                   | apply ThreeSumApsp.Scale.SoftO.sub
                   | apply ThreeSumApsp.Scale.SoftO.div)
           (·
               first
               | decide
               | exact isEmptyElim))
       | ( (fail_if_success
               (fail_if_success
                   ( (apply ThreeSumApsp.Scale.SoftO.mono)
                     (on_goal 1 =>
                         ((repeat'
                               with_reducible
                                 first
                                 | exact ThreeSumApsp.Scale.SoftO.const _
                                 | apply Light.PolyBounded.fst
                                 | apply Light.PolyBounded.snd
                                 | apply ThreeSumApsp.Scale.SoftO.log
                                 | apply ThreeSumApsp.Scale.SoftO.sqrt
                                 | apply hD
                                 | apply ThreeSumApsp.Scale.SoftO.add
                                 | apply ThreeSumApsp.Scale.SoftO.mul
                                 | apply ThreeSumApsp.Scale.SoftO.pow
                                 | apply ThreeSumApsp.Scale.SoftO.max
                                 | apply ThreeSumApsp.Scale.SoftO.sub
                                 | apply ThreeSumApsp.Scale.SoftO.div);
                           (done))))))
           (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le)
           (all_goals
               try (
                   (apply ThreeSumApsp.Scale.SoftO.mono)
                   (·
                       repeat'
                         with_reducible
                           first
                           | exact ThreeSumApsp.Scale.SoftO.const _
                           | apply Light.PolyBounded.fst
                           | apply Light.PolyBounded.snd
                           | apply ThreeSumApsp.Scale.SoftO.log
                           | apply ThreeSumApsp.Scale.SoftO.sqrt
                           | apply hD
                           | apply ThreeSumApsp.Scale.SoftO.add
                           | apply ThreeSumApsp.Scale.SoftO.mul
                           | apply ThreeSumApsp.Scale.SoftO.pow
                           | apply ThreeSumApsp.Scale.SoftO.max
                           | apply ThreeSumApsp.Scale.SoftO.sub
                           | apply ThreeSumApsp.Scale.SoftO.div)
                   (· decide))))
       | ( (apply ThreeSumApsp.Scale.SoftO.mono)
           (·
               repeat'
                 with_reducible
                   first
                   | exact ThreeSumApsp.Scale.SoftO.const _
                   | apply Light.PolyBounded.fst
                   | apply Light.PolyBounded.snd
                   | apply ThreeSumApsp.Scale.SoftO.log
                   | apply ThreeSumApsp.Scale.SoftO.sqrt
                   | apply hD
                   | apply ThreeSumApsp.Scale.SoftO.add
                   | apply ThreeSumApsp.Scale.SoftO.mul
                   | apply ThreeSumApsp.Scale.SoftO.pow
                   | apply ThreeSumApsp.Scale.SoftO.max
                   | apply ThreeSumApsp.Scale.SoftO.sub
                   | apply ThreeSumApsp.Scale.SoftO.div))) : PolyBounded fun n _ => D n ^ c + 1).of_le fun n _ => paramGr_le_succ _

private theorem polyBounded_wDr (hb : 1 ≤ b) (hab : a ≤ b) : PolyBounded fun n _ => wDr a b n := by
  unfold wDr
  (first
   | ( (apply ThreeSumApsp.Scale.SoftO.mono)
       (·
           repeat'
             with_reducible
               first
               | exact ThreeSumApsp.Scale.SoftO.const _
               | apply Light.PolyBounded.fst
               | apply Light.PolyBounded.snd
               | apply ThreeSumApsp.Scale.SoftO.log
               | apply ThreeSumApsp.Scale.SoftO.sqrt
               | apply polyBounded_paramDr hb hab
               | apply PolyBounded.fst
               | apply ThreeSumApsp.Scale.SoftO.add
               | apply ThreeSumApsp.Scale.SoftO.mul
               | apply ThreeSumApsp.Scale.SoftO.pow
               | apply ThreeSumApsp.Scale.SoftO.max
               | apply ThreeSumApsp.Scale.SoftO.sub
               | apply ThreeSumApsp.Scale.SoftO.div)
       (·
           first
           | decide
           | exact isEmptyElim))
   | ( (fail_if_success
           (fail_if_success
               ( (apply ThreeSumApsp.Scale.SoftO.mono)
                 (on_goal 1 =>
                     ((repeat'
                           with_reducible
                             first
                             | exact ThreeSumApsp.Scale.SoftO.const _
                             | apply Light.PolyBounded.fst
                             | apply Light.PolyBounded.snd
                             | apply ThreeSumApsp.Scale.SoftO.log
                             | apply ThreeSumApsp.Scale.SoftO.sqrt
                             | apply polyBounded_paramDr hb hab
                             | apply PolyBounded.fst
                             | apply ThreeSumApsp.Scale.SoftO.add
                             | apply ThreeSumApsp.Scale.SoftO.mul
                             | apply ThreeSumApsp.Scale.SoftO.pow
                             | apply ThreeSumApsp.Scale.SoftO.max
                             | apply ThreeSumApsp.Scale.SoftO.sub
                             | apply ThreeSumApsp.Scale.SoftO.div);
                       (done))))))
       (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le)
       (all_goals
           try (
               (apply ThreeSumApsp.Scale.SoftO.mono)
               (·
                   repeat'
                     with_reducible
                       first
                       | exact ThreeSumApsp.Scale.SoftO.const _
                       | apply Light.PolyBounded.fst
                       | apply Light.PolyBounded.snd
                       | apply ThreeSumApsp.Scale.SoftO.log
                       | apply ThreeSumApsp.Scale.SoftO.sqrt
                       | apply polyBounded_paramDr hb hab
                       | apply PolyBounded.fst
                       | apply ThreeSumApsp.Scale.SoftO.add
                       | apply ThreeSumApsp.Scale.SoftO.mul
                       | apply ThreeSumApsp.Scale.SoftO.pow
                       | apply ThreeSumApsp.Scale.SoftO.max
                       | apply ThreeSumApsp.Scale.SoftO.sub
                       | apply ThreeSumApsp.Scale.SoftO.div)
               (· decide))))
   | ( (apply ThreeSumApsp.Scale.SoftO.mono)
       (·
           repeat'
             with_reducible
               first
               | exact ThreeSumApsp.Scale.SoftO.const _
               | apply Light.PolyBounded.fst
               | apply Light.PolyBounded.snd
               | apply ThreeSumApsp.Scale.SoftO.log
               | apply ThreeSumApsp.Scale.SoftO.sqrt
               | apply polyBounded_paramDr hb hab
               | apply PolyBounded.fst
               | apply ThreeSumApsp.Scale.SoftO.add
               | apply ThreeSumApsp.Scale.SoftO.mul
               | apply ThreeSumApsp.Scale.SoftO.pow
               | apply ThreeSumApsp.Scale.SoftO.max
               | apply ThreeSumApsp.Scale.SoftO.sub
               | apply ThreeSumApsp.Scale.SoftO.div)))

private theorem polyBounded_wGr (hb : 1 ≤ b) (hab : a ≤ b) :
    PolyBounded fun n _ => wGr c e (paramDr a b n) := by
  unfold wGr
  (first
   | ( (apply ThreeSumApsp.Scale.SoftO.mono)
       (·
           repeat'
             with_reducible
               first
               | exact ThreeSumApsp.Scale.SoftO.const _
               | apply Light.PolyBounded.fst
               | apply Light.PolyBounded.snd
               | apply ThreeSumApsp.Scale.SoftO.log
               | apply ThreeSumApsp.Scale.SoftO.sqrt
               | apply polyBounded_paramDr hb hab
               | apply polyBounded_paramGr (c := c) (e := e) (polyBounded_paramDr hb hab)
               | apply ThreeSumApsp.Scale.SoftO.add
               | apply ThreeSumApsp.Scale.SoftO.mul
               | apply ThreeSumApsp.Scale.SoftO.pow
               | apply ThreeSumApsp.Scale.SoftO.max
               | apply ThreeSumApsp.Scale.SoftO.sub
               | apply ThreeSumApsp.Scale.SoftO.div)
       (·
           first
           | decide
           | exact isEmptyElim))
   | ( (fail_if_success
           (fail_if_success
               ( (apply ThreeSumApsp.Scale.SoftO.mono)
                 (on_goal 1 =>
                     ((repeat'
                           with_reducible
                             first
                             | exact ThreeSumApsp.Scale.SoftO.const _
                             | apply Light.PolyBounded.fst
                             | apply Light.PolyBounded.snd
                             | apply ThreeSumApsp.Scale.SoftO.log
                             | apply ThreeSumApsp.Scale.SoftO.sqrt
                             | apply polyBounded_paramDr hb hab
                             | apply polyBounded_paramGr (c := c) (e := e) (polyBounded_paramDr hb hab)
                             | apply ThreeSumApsp.Scale.SoftO.add
                             | apply ThreeSumApsp.Scale.SoftO.mul
                             | apply ThreeSumApsp.Scale.SoftO.pow
                             | apply ThreeSumApsp.Scale.SoftO.max
                             | apply ThreeSumApsp.Scale.SoftO.sub
                             | apply ThreeSumApsp.Scale.SoftO.div);
                       (done))))))
       (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le)
       (all_goals
           try (
               (apply ThreeSumApsp.Scale.SoftO.mono)
               (·
                   repeat'
                     with_reducible
                       first
                       | exact ThreeSumApsp.Scale.SoftO.const _
                       | apply Light.PolyBounded.fst
                       | apply Light.PolyBounded.snd
                       | apply ThreeSumApsp.Scale.SoftO.log
                       | apply ThreeSumApsp.Scale.SoftO.sqrt
                       | apply polyBounded_paramDr hb hab
                       | apply polyBounded_paramGr (c := c) (e := e) (polyBounded_paramDr hb hab)
                       | apply ThreeSumApsp.Scale.SoftO.add
                       | apply ThreeSumApsp.Scale.SoftO.mul
                       | apply ThreeSumApsp.Scale.SoftO.pow
                       | apply ThreeSumApsp.Scale.SoftO.max
                       | apply ThreeSumApsp.Scale.SoftO.sub
                       | apply ThreeSumApsp.Scale.SoftO.div)
               (· decide))))
   | ( (apply ThreeSumApsp.Scale.SoftO.mono)
       (·
           repeat'
             with_reducible
               first
               | exact ThreeSumApsp.Scale.SoftO.const _
               | apply Light.PolyBounded.fst
               | apply Light.PolyBounded.snd
               | apply ThreeSumApsp.Scale.SoftO.log
               | apply ThreeSumApsp.Scale.SoftO.sqrt
               | apply polyBounded_paramDr hb hab
               | apply polyBounded_paramGr (c := c) (e := e) (polyBounded_paramDr hb hab)
               | apply ThreeSumApsp.Scale.SoftO.add
               | apply ThreeSumApsp.Scale.SoftO.mul
               | apply ThreeSumApsp.Scale.SoftO.pow
               | apply ThreeSumApsp.Scale.SoftO.max
               | apply ThreeSumApsp.Scale.SoftO.sub
               | apply ThreeSumApsp.Scale.SoftO.div)))

private theorem steps_paramDr (hb : 1 ≤ b) (hab : a ≤ b) :
    StepsMon (fun θ => paramDr a b θ.n) 1 0 0 :=
  steps_n.of_le fun _ hθ => paramDr_le hb hab hθ.one_le_n_nat

private theorem steps_tDr (hb : 1 ≤ b) (hab : a ≤ b) : StepsMon (fun θ => tDr a b θ.n) 1 0 0 := by
  unfold tDr
  (first
   | ( (apply ThreeSumApsp.Scale.SoftO.mono)
       (·
           repeat'
             with_reducible
               first
               | exact ThreeSumApsp.Scale.SoftO.const _
               | apply steps_paramDr hb hab
               | apply ThreeSumApsp.Scale.SoftO.add
               | apply ThreeSumApsp.Scale.SoftO.mul
               | apply ThreeSumApsp.Scale.SoftO.pow
               | apply ThreeSumApsp.Scale.SoftO.max
               | apply ThreeSumApsp.Scale.SoftO.sub
               | apply ThreeSumApsp.Scale.SoftO.div)
       (·
           first
           | decide
           | exact isEmptyElim))
   | ( (fail_if_success
           (fail_if_success
               ( (apply ThreeSumApsp.Scale.SoftO.mono)
                 (on_goal 1 =>
                     ((repeat'
                           with_reducible
                             first
                             | exact ThreeSumApsp.Scale.SoftO.const _
                             | apply steps_paramDr hb hab
                             | apply ThreeSumApsp.Scale.SoftO.add
                             | apply ThreeSumApsp.Scale.SoftO.mul
                             | apply ThreeSumApsp.Scale.SoftO.pow
                             | apply ThreeSumApsp.Scale.SoftO.max
                             | apply ThreeSumApsp.Scale.SoftO.sub
                             | apply ThreeSumApsp.Scale.SoftO.div);
                       (done))))))
       (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le)
       (all_goals
           try (
               (apply ThreeSumApsp.Scale.SoftO.mono)
               (·
                   repeat'
                     with_reducible
                       first
                       | exact ThreeSumApsp.Scale.SoftO.const _
                       | apply steps_paramDr hb hab
                       | apply ThreeSumApsp.Scale.SoftO.add
                       | apply ThreeSumApsp.Scale.SoftO.mul
                       | apply ThreeSumApsp.Scale.SoftO.pow
                       | apply ThreeSumApsp.Scale.SoftO.max
                       | apply ThreeSumApsp.Scale.SoftO.sub
                       | apply ThreeSumApsp.Scale.SoftO.div)
               (· decide))))
   | ( (apply ThreeSumApsp.Scale.SoftO.mono)
       (·
           repeat'
             with_reducible
               first
               | exact ThreeSumApsp.Scale.SoftO.const _
               | apply steps_paramDr hb hab
               | apply ThreeSumApsp.Scale.SoftO.add
               | apply ThreeSumApsp.Scale.SoftO.mul
               | apply ThreeSumApsp.Scale.SoftO.pow
               | apply ThreeSumApsp.Scale.SoftO.max
               | apply ThreeSumApsp.Scale.SoftO.sub
               | apply ThreeSumApsp.Scale.SoftO.div)))

private theorem steps_tGr (he : 1 ≤ e) (hce : c ≤ e) : StepsMon (fun θ => tGr c e θ.D) 0 2 0 := by
  have hg : StepsMon (fun θ => paramGr c e θ.D) 0 2 0 :=
    steps_D.of_le fun _ hθ => paramGr_le he hce hθ.one_le_D_nat
  unfold tGr
  (first
   | ( (apply ThreeSumApsp.Scale.SoftO.mono)
       (·
           repeat'
             with_reducible
               first
               | exact ThreeSumApsp.Scale.SoftO.const _
               | apply hg
               | apply ThreeSumApsp.Scale.SoftO.add
               | apply ThreeSumApsp.Scale.SoftO.mul
               | apply ThreeSumApsp.Scale.SoftO.pow
               | apply ThreeSumApsp.Scale.SoftO.max
               | apply ThreeSumApsp.Scale.SoftO.sub
               | apply ThreeSumApsp.Scale.SoftO.div)
       (·
           first
           | decide
           | exact isEmptyElim))
   | ( (fail_if_success
           (fail_if_success
               ( (apply ThreeSumApsp.Scale.SoftO.mono)
                 (on_goal 1 =>
                     ((repeat'
                           with_reducible
                             first
                             | exact ThreeSumApsp.Scale.SoftO.const _
                             | apply hg
                             | apply ThreeSumApsp.Scale.SoftO.add
                             | apply ThreeSumApsp.Scale.SoftO.mul
                             | apply ThreeSumApsp.Scale.SoftO.pow
                             | apply ThreeSumApsp.Scale.SoftO.max
                             | apply ThreeSumApsp.Scale.SoftO.sub
                             | apply ThreeSumApsp.Scale.SoftO.div);
                       (done))))))
       (repeat' with_reducible apply ThreeSumApsp.Scale.SoftO.add_le)
       (all_goals
           try (
               (apply ThreeSumApsp.Scale.SoftO.mono)
               (·
                   repeat'
                     with_reducible
                       first
                       | exact ThreeSumApsp.Scale.SoftO.const _
                       | apply hg
                       | apply ThreeSumApsp.Scale.SoftO.add
                       | apply ThreeSumApsp.Scale.SoftO.mul
                       | apply ThreeSumApsp.Scale.SoftO.pow
                       | apply ThreeSumApsp.Scale.SoftO.max
                       | apply ThreeSumApsp.Scale.SoftO.sub
                       | apply ThreeSumApsp.Scale.SoftO.div)
               (· decide))))
   | ( (apply ThreeSumApsp.Scale.SoftO.mono)
       (·
           repeat'
             with_reducible
               first
               | exact ThreeSumApsp.Scale.SoftO.const _
               | apply hg
               | apply ThreeSumApsp.Scale.SoftO.add
               | apply ThreeSumApsp.Scale.SoftO.mul
               | apply ThreeSumApsp.Scale.SoftO.pow
               | apply ThreeSumApsp.Scale.SoftO.max
               | apply ThreeSumApsp.Scale.SoftO.sub
               | apply ThreeSumApsp.Scale.SoftO.div)))

end params

/-- The full-D Theorem 17 host for rational power parameters, together with the exact
floor/ceiling characterization of the chosen parameters. -/
theorem full_d_parameter_host (a b c e : ℕ) (hb : 1 ≤ b) (he : 1 ≤ e)
    (hab : a ≤ b) (hce : 2 * c ≤ e) :
    Claim.Theorem_17 lightModel strassen (fun n => paramDr a b n)
      (fun n => paramGr c e (paramDr a b n)) ∧
      (∀ n, paramDr a b n = ⌊(n : ℝ) ^ ((a : ℝ) / b)⌋₊) ∧
      (∀ D, 1 ≤ D → paramGr c e D = ⌈(D : ℝ) ^ ((c : ℝ) / e)⌉₊) := by
  refine ⟨?_, ?_, ?_⟩
  · have hce' : c ≤ e := by omega
    refine claim17_of_host strassen (fun n => paramDr a b n)
      (fun n => paramGr c e (paramDr a b n))
      (hostTime (paramDr a b) (paramGr c e) (tDr a b) (tGr c e))
      (hostNeed (paramDr a b) (paramGr c e) (wDr a b) (wGr c e))
      (fun Q pS Tn r hr hs => ?_)
      (obeysBound17_hostTime _ _ (fun _ => rfl) (fun _ _ => rfl)
        (steps_tDr hb hab).withinBuild (steps_tGr he hce').withinBuild)
    have h := et17_solves (P₀ := Q ++ ratParamProcs a b c e Q.length) (hs.append _)
      (paramProc_dr hb Q) (paramProc_gr he Q) (fun _ hn => one_le_paramDr hb hn)
    rw [List.append_assoc] at h
    exact ⟨_, _, h, hostNeed_poly (polyBounded_paramDr hb hab)
      (polyBounded_paramGr (polyBounded_paramDr hb hab)) (polyBounded_wDr hb hab)
      (polyBounded_wGr hb hab) hr⟩
  · intro n
    exact paramDr_eq_floor hb n
  · intro D hD
    exact paramGr_eq_ceil he hD

end Light.Sec3
end

#print axioms Light.Sec3.full_d_parameter_host

theorem solution (a b c e : ℕ) (hb : 1 ≤ b) (he : 1 ≤ e)
    (hab : a ≤ b) (hce : 2 * c ≤ e) :
    ThreeSumApsp.Claim.Theorem_17 Light.lightModel ThreeSumApsp.strassen
      (fun n => ThreeSumApsp.paramDr a b n)
      (fun n => ThreeSumApsp.paramGr c e (ThreeSumApsp.paramDr a b n)) ∧
      (∀ n, ThreeSumApsp.paramDr a b n = ⌊(n : ℝ) ^ ((a : ℝ) / b)⌋₊) ∧
      (∀ D, 1 ≤ D → ThreeSumApsp.paramGr c e D = ⌈(D : ℝ) ^ ((c : ℝ) / e)⌉₊) :=
  Light.Sec3.full_d_parameter_host a b c e hb he hab hce

#print axioms solution
