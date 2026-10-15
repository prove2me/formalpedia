-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSumApsp.FromClaims.solvedAt_of_realized
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:15:45.82288+00:00
-- url     : https://prove2.me/submissions/c1036289-f58b-4d4b-8696-65a9b33f234a

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Ceil
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSumApsp_Dominated_of_eventually

namespace Asymptotics
end Asymptotics
namespace Filter
end Filter
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSum1960614.Machine.ThreeSumApsp.Dominated
end ThreeSum1960614.Machine.ThreeSumApsp.Dominated
namespace ThreeSum1960614.Machine.ThreeSumApsp.FromClaims
end ThreeSum1960614.Machine.ThreeSumApsp.FromClaims
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Dominated
end ThreeSumApsp.Dominated
namespace ThreeSumApsp.FromClaims
end ThreeSumApsp.FromClaims
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

namespace ThreeSum1960614.Machine

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

open _root_.Filter
open _root_.Asymptotics

namespace ThreeSumApsp
open _root_.ThreeSumApsp




namespace Dominated
open _root_.ThreeSumApsp.Dominated


variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}

/-! ### Entering the calculus -/













/-! ### Leaving the calculus -/



/-! ### Chaining, restricting, substituting -/



/-- A bound holds on every smaller domain. -/
theorem mono_dom (hfg : _root_.ThreeSum1960614.Machine.ThreeSumApsp.Dominated dom f g) (hdom : ∀ x, dom' x → dom x) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.Dominated dom' f g := by
  obtain ⟨C, hC, hf⟩ := hfg
  exact ⟨C, hC, fun x hx => hf x (hdom x hx)⟩









/-! ### Sums and case distinctions -/







/-! ### Products and quotients -/

















/-! ### Functions of one natural number -/



/-- A bound by a nonnegative `g` that holds from some unknown point on gives a bound by `g + 1`
everywhere. -/
theorem of_eventually_add_one {f g : ℕ → ℝ} {C : ℝ} (hfg : ∀ᶠ n in atTop, f n ≤ C * g n)
    (hg : ∀ n, 0 ≤ g n) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.Dominated (fun _ => True) f fun n => g n + 1 := by
  have hpos : ∀ n, 0 ≤ n → 0 < g n + 1 := fun n _ => add_pos_of_nonneg_of_pos (hg n) zero_lt_one
  refine (_root_.ThreeSum1960614.Machine.ThreeSumApsp.Dominated.of_eventually (C := |C|) (hfg.mono fun n hn => hn.trans ?_) hpos).mono_dom
    fun n _ => n.zero_le
  exact (mul_le_mul_of_nonneg_right (le_abs_self C) (hg n)).trans
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (abs_nonneg C))



end Dominated



end ThreeSumApsp

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.ThreeSumApsp.WordRam


open _root_.EndStatement renaming Instr -> Instr
open _root_.Filter

/-! ## The problems of the end statement as problems in the sense of `Problem` -/







/-- `EndStatement.Problem.SolvedBy` counts the output cells as `1 + len + i`, and `output` counts
them as `(len + 1) + i`. -/
theorem output_cons {W : ℕ} (c : ℤ → BitVec W) (n : ℤ) (l : List ℤ) :
    (fun i : ℕ => (c ((1 + l.length + i : ℕ) : ℤ)).toInt) = _root_.ThreeSumApsp.WordRam.output c (n :: l).length := by
  funext i
  simp only [_root_.ThreeSumApsp.WordRam.output, List.length_cons, Nat.add_comm 1]
  rfl

/-- `SolvesWithin` is `Solves` for the problem `ofEnd Q`, on the instances with `U = n^κ`. -/
theorem solvesWithin_iff {Q : _root_.EndStatement.Problem} {κ : ℕ} {P : List _root_.EndStatement.Instr} {b : ℕ} {T : ℕ → ℝ} :
    _root_.ThreeSumApsp.WordRam.SolvesWithin Q κ P b T ↔ _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Solves (_root_.ThreeSumApsp.WordRam.ofEnd Q) P b (fun x => x.U = x.n ^ κ) fun x => T x.n := by
  constructor
  · intro h x hx bits hbits
    obtain ⟨t, ht, verdict, m, hexec, hyes, hout⟩ :=
      h x.n x.x (hx ▸ x.bounded) bits (by simpa [_root_.ThreeSumApsp.WordRam.Admissible] using hbits)
    exact ⟨t, verdict, m, ht, hexec, hyes, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.output_cons m x.n (Q.input x.x) ▸ hout⟩
  · intro h n x hx W hW
    obtain ⟨t, verdict, c, ht, hrun, hyes, hout⟩ :=
      h ⟨n, n ^ κ, x, hx⟩ rfl W (by simpa [_root_.ThreeSumApsp.WordRam.Admissible] using hW)
    exact ⟨t, ht, verdict, c, hrun, hyes, (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.output_cons c n (Q.input x)).symm ▸ hout⟩

/-- `SolvedInTimeAt` in terms of `Solves`. -/
theorem solvedInTimeAt_iff {Q : _root_.EndStatement.Problem} {κ : ℕ} {a : ℝ} {e : ℕ} :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.SolvedInTimeAt Q κ a e ↔ ∃ (P : List _root_.EndStatement.Instr) (b : ℕ) (C : ℝ),
      _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Solves (_root_.ThreeSumApsp.WordRam.ofEnd Q) P b (fun x => x.U = x.n ^ κ)
        fun x => C * ((x.n : ℝ) ^ a * Real.log x.n ^ e + 1) := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.SolvedInTimeAt, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.solvesWithin_iff]

/-! ## Monotonicity -/

/-- `Solves` stays true for a larger slope, a smaller set of instances and a larger time bound. -/
theorem Solves.mono {prob : _root_.ThreeSumApsp.WordRam.Problem} {P : List _root_.EndStatement.Instr} {b b' : ℕ} {dom dom' : prob.Inst → Prop}
    {T T' : prob.Inst → ℝ} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Solves prob P b dom T) (hb : b ≤ b') (hdom : ∀ x, dom' x → dom x)
    (hT : ∀ x, dom' x → T x ≤ T' x) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Solves prob P b' dom' T' := by
  intro x hx bits hadm
  obtain ⟨t, verdict, c, ht, he, ha⟩ :=
    h x (hdom x hx) bits (le_trans (Nat.mul_le_mul_right _ hb) hadm)
  exact ⟨t, verdict, c, ht.trans (hT x hx), he, ha⟩



/-! ## Bounds up to a constant -/





/-! ## Bounds in one size -/









end ThreeSumApsp.WordRam

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.ThreeSumApsp.FromClaims


open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam
open _root_.EndStatement renaming Instr -> Instr

/-! ## Bounds on a domain -/



/-- The bound `U = N^c` on the numbers, as a real number. -/
theorem cast_pow_eq (N c : ℕ) : ((N ^ c : ℕ) : ℝ) = (N : ℝ) ^ ((c : ℕ) : ℝ) := by
  rw [Real.rpow_natCast]
  push_cast
  rfl







/-! ## Bounds in one size, for all large sizes -/











end ThreeSumApsp.FromClaims

end

end ThreeSum1960614.Machine

section
open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp

open _root_.ThreeSum1960614.Machine.ThreeSumApsp.FromClaims

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam
open _root_.EndStatement renaming Instr -> Instr
section

/-- From a realized running time with a bound for all large sizes to a program with that bound. -/
theorem ThreeSum1960614.Machine.ThreeSumApsp.FromClaims.solvedAt_of_realized__implementation_3cf9a65dc2 {Q : _root_.EndStatement.Problem} (T : ℕ → ℝ → ℝ) (κ : ℕ)
    (hR : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Realized Q T) {C a : ℝ} {e : ℕ}
    (hev : ∀ᶠ n : ℕ in Filter.atTop,
      T n ((n : ℝ) ^ ((κ : ℕ) : ℝ)) ≤ C * ((n : ℝ) ^ a * Real.log n ^ e)) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.SolvedInTimeAt Q κ a e := by
  obtain ⟨P, b, c, hc, hS⟩ := hR κ
  have hg : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ a * Real.log n ^ e := fun n =>
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Real.log_natCast_nonneg _) _)
  -- a bound for all large `n` gives a bound for all `n`
  obtain ⟨C', hC', hb⟩ := _root_.ThreeSum1960614.Machine.ThreeSumApsp.Dominated.of_eventually_add_one hev hg
  refine _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.solvedInTimeAt_iff.2 ⟨P, b, c * C' + c, hS.mono le_rfl (fun x hx => hx) fun x hx => ?_⟩
  have hU : ((x.U : ℕ) : ℝ) = (x.n : ℝ) ^ ((κ : ℕ) : ℝ) := by
    rw [hx]
    exact _root_.ThreeSum1960614.Machine.ThreeSumApsp.FromClaims.cast_pow_eq _ _
  change c * max (T x.n ((x.U : ℕ) : ℝ)) 0 + c ≤ _
  rw [hU]
  -- `c max(T, 0) + c ≤ c C' (X + 1) + c ≤ (c C' + c) (X + 1)`, where `X = n^a (log n)^e ≥ 0`
  have hcT : c * max (T x.n ((x.n : ℝ) ^ ((κ : ℕ) : ℝ))) 0 ≤
      c * (C' * ((x.n : ℝ) ^ a * Real.log x.n ^ e + 1)) :=
    mul_le_mul_of_nonneg_left (max_le (hb x.n trivial) (mul_nonneg hC' (by linarith [hg x.n]))) hc
  linarith [mul_nonneg hc (hg x.n)]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSumApsp.FromClaims.solvedAt_of_realized__implementation_3cf9a65dc2) := (@ThreeSum1960614.Machine.ThreeSumApsp.FromClaims.solvedAt_of_realized__implementation_3cf9a65dc2)

#print axioms solution
