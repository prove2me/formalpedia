-- Prove2me | solution 1 for ThreeSumSharpTail.full_d_uniformize
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T20:47:57.762261+00:00
-- url     : https://prove2.me/submissions/bce75b4a-1650-4a2f-9256-7ace6ff7f8cc

import Mathlib
import Definitions.Def_APSP299791_Defs5
import Theorems.Thm_Light_Sec3_claim_exactTriangleUniform_usingCorollary26
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
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Instances
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Theorem19
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Theorem21_22
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Ceil
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSumSource_ReductionClaims




set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false



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

namespace ThreeSumApsp

end ThreeSumApsp
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
open ThreeSumApsp

namespace ThreeSumApsp

namespace List
theorem getD_of_forall_mem_local {α : Type*} {p : α → Prop} {l : List α} {d : α}
    (hd : p d) (h : ∀ x ∈ l, p x) (i : ℕ) : p (l.getD i d) := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem l d hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default l d hi]
    exact hd
end List

theorem AbsLe.abs_getD_le {l : List ℤ} {U : ℤ} (hU : 0 ≤ U) (h : AbsLe l U) (i : ℕ) :
    |l.getD i 0| ≤ U :=
  List.getD_of_forall_mem_local (p := fun x => |x| ≤ U) (by rwa [abs_zero]) h i

theorem AbsLe.getElem {l : List ℤ} {U : ℤ} (h : AbsLe l U) {i : ℕ} (hi : i < l.length) :
    |l[i]| ≤ U := h _ (List.getElem_mem hi)

end ThreeSumApsp

namespace Light

variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}

namespace ArrayAt
theorem listAt (h : ArrayAt μ a l N U top) : ListAt μ a l N top := { h with }
theorem read (h : ArrayAt μ a l N U top) (hi : i < N) : μ (a + i) = l.getD i 0 :=
  h.seg.getD (h.len ▸ hi) 0
theorem abs_read_le (h : ArrayAt μ a l N U top) (hi : i < N) : |μ (a + i)| ≤ U := by
  rw [h.seg i (h.len ▸ hi)]
  exact h.bound.getElem _
end ArrayAt

theorem frame_append_zeros (l : List ℤ) (n : ℕ) :
    frame (l ++ List.replicate n 0) = frame l := by
  funext y
  simp only [frame, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split_ifs with h1 h2
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega)]

theorem Program.getElem?_behind_right {P : Program} (Q : Program) {p : ℕ} {body : Stmt}
    (h : P[p]? = some body) : (Program.behind Q P)[p + Q.length]? = some (body.shift Q.length) := by
  rw [Program.behind, List.getElem?_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel,
    List.getElem?_map, h]
  rfl

theorem Exec.shift {P : Program} {lim : Limits} {d : ℕ} {s : Stmt} {σ σ' : State} {c : ℕ}
    (h : Exec lim P d s σ σ' c) (Q : Program) :
    Exec lim (Program.behind Q P) d (s.shift Q.length) σ σ' c := by
  induction h with
  | skip => exact .skip
  | set h => exact .set h
  | store h₁ h₂ h₃ => exact .store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact .iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact .iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact .whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact .whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact .call h₁ (Program.getElem?_behind_right Q h₂) h₃ ih

theorem Ends.shift {P : Program} {lim : Limits} {d : ℕ} {s : Stmt} {σ : State} {T : ℕ}
    {post : State → Prop} (h : Ends lim P d s σ T post) (Q : Program) :
    Ends lim (Program.behind Q P) d (s.shift Q.length) σ T post := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he.shift Q, hc, hq⟩

theorem Ends.shift_append {P : Program} {lim : Limits} {d : ℕ} {s : Stmt} {σ : State} {T : ℕ}
    {post : State → Prop} (h : Ends lim P d s σ T post) (Q R : Program) :
    Ends lim (Program.behind Q P ++ R) d (s.shift Q.length) σ T post :=
  (h.shift Q).append R

theorem Exec.shift_append {P : Program} {lim : Limits} {d : ℕ} {s : Stmt} {σ σ' : State} {c : ℕ}
    (h : Exec lim P d s σ σ' c) (Q R : Program) :
    Exec lim (Program.behind Q P ++ R) d (s.shift Q.length) σ σ' c :=
  (h.shift Q).append R

theorem Solves.meets {task : Task} {P₀ : Program} {p : ℕ} {T₀ : ℕ → ℕ → ℕ}
    {need : ℕ → ℕ → Need} (h : Solves task P₀ p T₀ need) (R : Program) {lim : Limits} {d : ℕ}
    (x : task.Inst) {μ : ℕ → ℤ} (fr : ℕ) (hpre : task.Pre x μ fr)
    (hok : (need (task.size x) (task.bound x)).Ok lim fr d) :
    Meets lim (P₀ ++ R) p d (task.args x ++ [(fr : ℤ)]) μ (T₀ (task.size x) (task.bound x))
      (task.Post x μ fr) := by
  obtain ⟨body, hp, hb⟩ := h
  exact ⟨body, getElem?_append_of_eq_some hp R, hb R lim d x μ fr hpre hok⟩

theorem SolvedIn.mono {task : Task} {T T' : ℕ → ℝ → ℝ} (h : SolvedIn task T)
    (hT : ∀ (n : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ u → T n u ≤ T' n u) : SolvedIn task T' := by
  obtain ⟨P, p, Tn, need, h1, h2, h3⟩ := h
  refine ⟨P, p, Tn, need, h1, h2, fun n U u hn hU hu => (h3 n U u hn hU hu).trans (hT n u hn ?_)⟩
  exact le_trans (by exact_mod_cast hU) hu

end Light

namespace ThreeSumApsp
theorem flag_congr {p q : Prop} (h : p ↔ q) : flag p = flag q := by
  rw [propext h]

theorem one_le_one_add_logU (u : ℝ) : 1 ≤ 1 + logU u := by
  have hu : 0 < logU u := (Real.log_pos one_lt_two).trans_le (Real.log_le_log two_pos (le_max_right _ _))
  linarith

theorem log_le_logU {u : ℝ} (hu : 0 < u) : Real.log u ≤ logU u :=
  Real.log_le_log hu (le_max_left _ _)

theorem one_le_log_add_one_pow (s e : ℕ) : 1 ≤ (Real.log s + 1) ^ e :=
  one_le_pow₀ (le_add_of_nonneg_left (Real.log_natCast_nonneg s))

end ThreeSumApsp

namespace Light
theorem Solves.append {task : Task} {P : Program} {p : ℕ} {T : ℕ → ℕ → ℕ}
    {need : ℕ → ℕ → Need} (h : Solves task P p T need) (R : Program) :
    Solves task (P ++ R) p T need := by
  obtain ⟨body, hp, hb⟩ := h
  refine ⟨body, getElem?_append_of_eq_some hp R,
    fun R' lim d x μ fr hpre hok => ?_⟩
  rw [List.append_assoc]
  exact hb (R ++ R') lim d x μ fr hpre hok
end Light

theorem closure_monoExactTriangle_local : Closure.MonoExactTriangle Light.lightModel :=
  fun _ _ hle hT => Light.SolvedIn.mono hT hle

namespace Light.Sec3.ChooseBySizeLocal

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

theorem solves_behind {task : Task} {P₀ : Program} {p : ℕ} {T : ℕ → ℕ → ℕ}
    {need : ℕ → ℕ → Need} (h : Solves task P₀ p T need) (Q : Program) :
    Solves task (Program.behind Q P₀) (p + Q.length) T need := by
  obtain ⟨body, hp, hb⟩ := h
  refine ⟨body.shift Q.length, Program.getElem?_behind_right Q hp,
    fun R lim d x μ fr hpre hok => ?_⟩
  have hh := hb [] lim d x μ fr hpre hok
  rw [List.append_nil] at hh
  obtain ⟨σ', c, he, hc, hp⟩ := hh
  exact ⟨σ', c, he.shift_append Q R, hc, hp⟩

theorem bySize_spec {P₀ R : Program} {n₀ p₁ p₂ : ℕ}
    {T₁ T₂ : ℕ → ℕ → ℕ} {r₁ r₂ : ℕ → ℕ → Need}
    (h₁ : Solves etTask P₀ p₁ T₁ r₁) (h₂ : Solves etTask P₀ p₂ T₂ r₂)
    {x : TriInst} {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : x.Pre μ fr) (hok : (bySizeNeed n₀ r₁ r₂ x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (bySizeBody n₀ p₁ p₂)
      ⟨frame (etTask.args x ++ [(fr : ℤ)]), μ⟩ (bySizeTime n₀ T₁ T₂ x.n x.U)
      (fun σ' => etTask.Post x μ fr (σ'.loc 0) σ'.mem) := by
  have hok₁ : (r₁ x.n x.U).Ok lim fr (d + 1) := hok.mono
    (by simp only [bySizeNeed]; omega) (by simp only [bySizeNeed]; omega)
    (by simp only [bySizeNeed]; omega)
  have hok₂ : (r₂ x.n x.U).Ok lim fr (d + 1) := hok.mono
    (by simp only [bySizeNeed]; omega) (by simp only [bySizeNeed]; omega)
    (by simp only [bySizeNeed]; omega)
  have hword : ((n₀ + (r₁ x.n x.U).word + (r₂ x.n x.U).word : ℕ) : ℤ) ≤ lim.word := hok.word
  have hdep : d + (1 + (r₁ x.n x.U).depth + (r₂ x.n x.U).depth) ≤ lim.depth := hok.depth
  have hm₁ : Meets lim (P₀ ++ R) p₁ (d + 1) [x.n, x.U, x.ab, x.bc, x.ac, fr] μ
      (T₁ x.n x.U) (etTask.Post x μ fr) := h₁.meets R x fr hpre hok₁
  have hm₂ : Meets lim (P₀ ++ R) p₂ (d + 1) [x.n, x.U, x.ab, x.bc, x.ac, fr] μ
      (T₂ x.n x.U) (etTask.Post x μ fr) := h₂.meets R x fr hpre hok₂
  change Ends lim (P₀ ++ R) d (bySizeBody n₀ p₁ p₂)
      ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr], μ⟩ _ _
  unfold bySizeTime
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_)
  · rw [if_pos (show x.n < n₀ by simp at hc; omega)]
    exact Ends.callTo hm₁ fun _ _ h => h
  · rw [if_neg (show ¬ x.n < n₀ by simp at hc; omega)]
    exact Ends.callTo hm₂ fun _ _ h => h

theorem polyNeed_bySize (n₀ : ℕ) {r₁ r₂ : ℕ → ℕ → Need}
    (h₁ : PolyNeed r₁) (h₂ : PolyNeed r₂) : PolyNeed (bySizeNeed n₀ r₁ r₂) := by
  obtain ⟨s₁, k₁, h₁⟩ := h₁
  obtain ⟨s₂, k₂, h₂⟩ := h₂
  refine ⟨s₁ + s₂ + n₀ + 2, k₁ + k₂, fun n U => ?_⟩
  let q := (n + 1) * (U + 1)
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow1 : q ^ k₁ ≤ q ^ (k₁ + k₂) := Nat.pow_le_pow_right hq (by omega)
  have hpow2 : q ^ k₂ ≤ q ^ (k₁ + k₂) := Nat.pow_le_pow_right hq (by omega)
  have hpow0 : 1 ≤ q ^ (k₁ + k₂) := Nat.one_le_pow _ _ hq
  have hs₁ : 2 ^ s₁ ≤ 2 ^ (s₁ + s₂ + n₀) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hs₂ : 2 ^ s₂ ≤ 2 ^ (s₁ + s₂ + n₀) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hsc : n₀ + 1 ≤ 2 ^ (s₁ + s₂ + n₀) :=
    (show n₀ + 1 ≤ 2 ^ n₀ by have h : n₀ < 2 ^ n₀ := Nat.lt_two_pow_self; omega).trans
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hbound₁ : polyBound s₁ k₁ [n, U] ≤
      2 ^ (s₁ + s₂ + n₀) * q ^ (k₁ + k₂) := by
    simpa [polyBound, q] using Nat.mul_le_mul hs₁ hpow1
  have hbound₂ : polyBound s₂ k₂ [n, U] ≤
      2 ^ (s₁ + s₂ + n₀) * q ^ (k₁ + k₂) := by
    simpa [polyBound, q] using Nat.mul_le_mul hs₂ hpow2
  have hboundC : n₀ + 1 ≤ 2 ^ (s₁ + s₂ + n₀) * q ^ (k₁ + k₂) :=
    hsc.trans (Nat.le_mul_of_pos_right _ (by omega))
  obtain ⟨hw₁, hc₁, hd₁⟩ := h₁ n U
  obtain ⟨hw₂, hc₂, hd₂⟩ := h₂ n U
  have htarget : polyBound (s₁ + s₂ + n₀ + 2) (k₁ + k₂) [n, U] =
      4 * (2 ^ (s₁ + s₂ + n₀) * q ^ (k₁ + k₂)) := by
    simp only [polyBound, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [pow_add]
    dsimp [q]
    ring
  simp only [bySizeNeed, htarget]
  constructor
  · omega
  · constructor <;> omega

end Light.Sec3.ChooseBySizeLocal

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec Light.Sec3.ChooseBySizeLocal

theorem closure_chooseBySize_local : Closure.ChooseBySize Light.lightModel := by
  intro n₀
  refine ⟨12, fun T₁ T₂ hT₁ hT₂ => ?_⟩
  obtain ⟨Q₁, p₁, Tn₁, r₁, hr₁, hs₁, ht₁⟩ := hT₁
  obtain ⟨Q₂, p₂, Tn₂, r₂, hr₂, hs₂, ht₂⟩ := hT₂
  have g₁ : Solves etTask (Program.behind Q₁ Q₂) p₁ Tn₁ r₁ := hs₁.append _
  have g₂ : Solves etTask (Program.behind Q₁ Q₂) (p₂ + Q₁.length) Tn₂ r₂ :=
    solves_behind hs₂ Q₁
  refine ⟨Program.behind Q₁ Q₂ ++ [bySizeBody n₀ p₁ (p₂ + Q₁.length)],
    (Program.behind Q₁ Q₂).length, bySizeTime n₀ Tn₁ Tn₂, bySizeNeed n₀ r₁ r₂,
    polyNeed_bySize n₀ hr₁ hr₂, ?_, fun n U u hn hU hu => ?_⟩
  · refine ⟨bySizeBody n₀ p₁ (p₂ + Q₁.length), by simp,
      fun R lim d x μ fr hpre hok => ?_⟩
    rw [List.append_assoc]
    exact bySize_spec g₁ g₂ hpre hok
  · simp only [bySizeTime]
    push_cast
    split_ifs
    · linarith [ht₁ n U u hn hU hu]
    · linarith [ht₂ n U u hn hU hu]

end Light.Sec3

namespace ThreeSumApsp.Theorem19FullDUniformize

theorem small_uniform_bound (δ K₀ : ℝ) (e N : ℕ) (p : SizeBound)
    (hδ0 : 0 ≤ δ) (hK : 1 ≤ K₀)
    (hsmall : (1 ≤ p.s ∧ 1 ≤ p.u) ∧ p.s < N) :
    K₀ * uniformShape (7 / 4000) 1 p ≤
      (K₀ * (N : ℝ) ^ δ * (Real.log N + 1)) * uniformShape δ e p := by
  have hs : (1 : ℝ) ≤ p.s := by exact_mod_cast hsmall.1.1
  have hspos : 0 < (p.s : ℝ) := by linarith
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : 0 < (N : ℝ) := by linarith
  have hsN : (p.s : ℝ) ≤ N := by exact_mod_cast hsmall.2.le
  have hlog0 : 0 ≤ Real.log p.s := Real.log_nonneg hs
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN
  have hlog : Real.log p.s + 1 ≤ Real.log N + 1 := by
    simpa only [add_comm] using add_le_add_right (Real.log_le_log hspos hsN) 1
  have hloge : 1 ≤ (Real.log p.s + 1) ^ e := one_le_pow₀ (by linarith)
  have hlogfactor : Real.log p.s + 1 ≤
      (Real.log N + 1) * (Real.log p.s + 1) ^ e := by
    calc
      _ ≤ Real.log N + 1 := hlog
      _ ≤ (Real.log N + 1) * (Real.log p.s + 1) ^ e :=
        le_mul_of_one_le_right (by linarith) hloge
  have hpow : (p.s : ℝ) ^ (3 - (7 / 4000 : ℝ)) ≤
      (p.s : ℝ) ^ (3 - δ) * (N : ℝ) ^ δ := by
    calc
      _ ≤ (p.s : ℝ) ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hs (by norm_num)
      _ = (p.s : ℝ) ^ (3 - δ) * (p.s : ℝ) ^ δ := by
        rw [← Real.rpow_add hspos]
        congr 1
        ring
      _ ≤ (p.s : ℝ) ^ (3 - δ) * (N : ℝ) ^ δ := by
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hspos.le hsN hδ0)
          (Real.rpow_nonneg hspos.le _)
  have hbase : (p.s : ℝ) ^ (3 - (7 / 4000 : ℝ)) * (Real.log p.s + 1) ≤
      ((p.s : ℝ) ^ (3 - δ) * (N : ℝ) ^ δ) *
        ((Real.log N + 1) * (Real.log p.s + 1) ^ e) := by
    exact mul_le_mul hpow hlogfactor (by linarith) (by positivity)
  have hweight : 0 ≤ (1 + logU p.u) ^ 2 := sq_nonneg _
  have hK0 : 0 ≤ K₀ := by linarith
  unfold uniformShape
  simp only [pow_one]
  calc
    _ ≤ K₀ * ((((p.s : ℝ) ^ (3 - δ) * (N : ℝ) ^ δ) *
      ((Real.log N + 1) * (Real.log p.s + 1) ^ e)) * (1 + logU p.u) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbase hweight) hK0
    _ = _ := by ring

theorem large_uniform_bound (δ K : ℝ) (e n₀ : ℕ) (T : ℕ → ℝ → ℝ)
    (hb : ∀ (n : ℕ) (κ u : ℝ), n₀ ≤ n → 1 ≤ κ → u ≤ (n : ℝ) ^ κ →
      T n u ≤ K * (κ * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e)))
    (n : ℕ) (u : ℝ) (hn : n₀ ≤ n) (h3 : 3 ≤ n) (hu : 1 ≤ u) :
    T n u ≤ max 1 K * uniformShape δ e ⟨n, u⟩ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlogn : 1 ≤ Real.log n := Real.one_le_log_natCast_of_three_le h3
  have hup : 0 < u := by linarith
  have hword0 : 0 ≤ logU u := by
    unfold logU
    apply Real.log_nonneg
    exact le_trans (by norm_num) (le_max_right u 2)
  have hword1 : 1 ≤ 1 + logU u := by linarith
  have hulog : Real.log u ≤ logU u :=
    Real.log_le_log hup (le_max_left u 2)
  have hκ : max 1 (Real.log u / Real.log n) ≤ (1 + logU u) ^ 2 := by
    apply le_trans (b := 1 + logU u)
    · apply max_le hword1
      have hdiv : Real.log u / Real.log n ≤ Real.log u :=
        div_le_self (Real.log_nonneg hu) hlogn
      linarith
    · exact le_self_pow₀ hword1 two_ne_zero
  have hweight : u ≤ (n : ℝ) ^ max 1 (Real.log u / Real.log n) := by
    calc
      u = (n : ℝ) ^ (Real.log u / Real.log n) := by
        rw [Real.rpow_def_of_pos hnpos, mul_div_cancel₀ _ (by linarith), Real.exp_log hup]
      _ ≤ (n : ℝ) ^ max 1 (Real.log u / Real.log n) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (le_max_right _ _)
  have hbase0 : 0 ≤ max 1 (Real.log u / Real.log n) *
      ((n : ℝ) ^ (3 - δ) * Real.log n ^ e) := by positivity
  have hbase : max 1 (Real.log u / Real.log n) *
      ((n : ℝ) ^ (3 - δ) * Real.log n ^ e) ≤ uniformShape δ e ⟨n, u⟩ := by
    calc
      _ ≤ (1 + logU u) ^ 2 * ((n : ℝ) ^ (3 - δ) * (Real.log n + 1) ^ e) := by
        gcongr
        linarith
      _ = _ := by unfold uniformShape; simp; ring
  calc
    T n u ≤ K * (max 1 (Real.log u / Real.log n) *
      ((n : ℝ) ^ (3 - δ) * Real.log n ^ e)) :=
        hb n _ u hn (le_max_left _ _) hweight
    _ ≤ max 1 K * (max 1 (Real.log u / Real.log n) *
      ((n : ℝ) ^ (3 - δ) * Real.log n ^ e)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hbase0
    _ ≤ _ := mul_le_mul_of_nonneg_left hbase (by positivity)

theorem uniformize_of_small_solver (M : DetTimeModel) (δ : ℝ) (e n₀ : ℕ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hex : Claim.Theorem_19_explicitAt M δ e n₀)
    (hold : Claim.ExactTriangleUniform M (7 / 4000) 1)
    (hchoose : Closure.ChooseBySize M) (hmono : Closure.MonoExactTriangle M) :
    Claim.ExactTriangleUniform M δ e := by
  obtain ⟨K, T, hT, hb⟩ := hex
  obtain ⟨K₀, hK₀, hT₀⟩ := hold
  let N : ℕ := max n₀ 3
  obtain ⟨C₀, hch⟩ := hchoose N
  let Csmall : ℝ := K₀ * (N : ℝ) ^ δ * (Real.log N + 1)
  let C : ℝ := 1 + Csmall + max 1 K + max 0 C₀
  have hN1 : (1 : ℝ) ≤ N := by
    exact_mod_cast (show 1 ≤ N by dsimp [N]; omega)
  have hCs : 0 ≤ Csmall := by
    dsimp [Csmall]
    exact mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith) _))
      (by linarith [Real.log_nonneg hN1])
  have hCl : 0 ≤ max 1 K := le_trans (by norm_num) (le_max_left _ _)
  have hCo : 0 ≤ max 0 C₀ := le_max_left _ _
  have hC1 : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC1, hmono _ _ (fun n u hn hu => ?_)
    (hch (uniformTime K₀ (7 / 4000) 1) T hT₀ hT)⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog1 : 1 ≤ Real.log n + 1 := by linarith [Real.log_nonneg hnR]
  have hwords1 : 1 ≤ 1 + logU u := by
    have hlogU : 0 ≤ logU u := Real.log_nonneg (le_trans (by norm_num) (le_max_right u 2))
    linarith
  have hshape1 : 1 ≤ uniformShape δ e ⟨n, u⟩ := by
    unfold uniformShape
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (Real.one_le_rpow hnR (by linarith)) (one_le_pow₀ hlog1))
      (one_le_pow₀ hwords1)
  have hshape0 : 0 ≤ uniformShape δ e ⟨n, u⟩ := by linarith
  have hbranch : (if n < N then uniformTime K₀ (7 / 4000) 1 n u else T n u) ≤
      (Csmall + max 1 K) * uniformShape δ e ⟨n, u⟩ := by
    by_cases hs : n < N
    · rw [if_pos hs]
      have hh := small_uniform_bound δ K₀ e N ⟨n, u⟩ hδ0 hK₀ ⟨⟨hn, hu⟩, hs⟩
      exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [Csmall]; linarith) hshape0)
    · rw [if_neg hs]
      have hnn₀ : n₀ ≤ n := by dsimp [N] at hs; omega
      have h3 : 3 ≤ n := by dsimp [N] at hs; omega
      exact (large_uniform_bound δ K e n₀ T hb n u hnn₀ h3 hu).trans
        (mul_le_mul_of_nonneg_right (by linarith) hshape0)
  have hcost : C₀ ≤ max 0 C₀ * uniformShape δ e ⟨n, u⟩ :=
    (le_max_right _ _).trans (le_mul_of_one_le_right hCo hshape1)
  change _ ≤ C * uniformShape δ e ⟨n, u⟩
  dsimp [C]
  nlinarith

end ThreeSumApsp.Theorem19FullDUniformize

theorem solution (δ : ℝ) (e n₀ : ℕ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hex : Claim.Theorem_19_explicitAt Light.lightModel δ e n₀) :
    Claim.ExactTriangleUniform Light.lightModel δ e := by
  have hold : Claim.ExactTriangleUniform Light.lightModel (7 / 4000) 1 := by
    convert Light.Sec3.claim_exactTriangleUniform_usingCorollary26 using 1 <;> norm_num
  exact ThreeSumApsp.Theorem19FullDUniformize.uniformize_of_small_solver
    Light.lightModel δ e n₀ hδ0 hδ1 hex
    hold Light.Sec3.closure_chooseBySize_local closure_monoExactTriangle_local

#print axioms solution
