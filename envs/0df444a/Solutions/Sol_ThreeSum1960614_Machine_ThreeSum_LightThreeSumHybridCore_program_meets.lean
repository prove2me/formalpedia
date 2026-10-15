-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:11:44.804492+00:00
-- url     : https://prove2.me/submissions/7ebba005-70fb-42cb-8219-221296a760c7

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
import Definitions.Def_ThreeSum1960614_Machine_Bundle026
import Definitions.Def_ThreeSum1960614_Machine_Bundle027
import Definitions.Def_ThreeSum1960614_Machine_Bundle028
import Definitions.Def_ThreeSum1960614_Machine_Bundle029
import Definitions.Def_ThreeSum1960614_Machine_Bundle030
import Definitions.Def_ThreeSum1960614_Machine_Bundle031
import Definitions.Def_ThreeSum1960614_Machine_Bundle032
import Definitions.Def_ThreeSum1960614_Machine_Bundle033
import Definitions.Def_ThreeSum1960614_Machine_Bundle034
import Definitions.Def_ThreeSum1960614_Machine_Bundle035
import Definitions.Def_ThreeSum1960614_Machine_Bundle036
import Definitions.Def_ThreeSum1960614_Machine_Bundle037
import Definitions.Def_ThreeSum1960614_Machine_Bundle038
import Definitions.Def_ThreeSum1960614_Machine_Bundle039
import Definitions.Def_ThreeSum1960614_Machine_Bundle040
import Definitions.Def_ThreeSum1960614_Machine_Bundle041
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_ThreeSum1962Source_Bundle17
import Definitions.Def_ThreeSum1962Source_Bundle18
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBruteThreeSum_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightNatPower_meets

local instance platformRadixNonzero_e178ab5469 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightBruteThreeSum
end ThreeSum.LightBruteThreeSum
namespace ThreeSum.LightThreeSumHybridCore
end ThreeSum.LightThreeSumHybridCore
namespace ThreeSum.ReportingHostRelocation
end ThreeSum.ReportingHostRelocation
namespace ThreeSum.ThreeSumFastResourcesHybrid
end ThreeSum.ThreeSumFastResourcesHybrid
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightBruteThreeSum
end ThreeSum1960614.Machine.ThreeSum.LightBruteThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
end ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid
end ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSum1960614.Machine.ThreeSumApsp.Spec
end ThreeSum1960614.Machine.ThreeSumApsp.Spec
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec

namespace ThreeSum1960614.Machine

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
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Runs -/

/-- A procedure of a program is a procedure, with the same number, of the program with more
procedures appended. -/
theorem getElem?_append_of_eq_some {P : _root_.ThreeSum1960614.Machine.Light.Program} {p : ℕ} {body : _root_.ThreeSum1960614.Machine.Light.Stmt} (h : P[p]? = some body)
    (R : _root_.ThreeSum1960614.Machine.Light.Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h





/-- A run stays a run when procedures are appended to the program. -/
theorem Exec.append {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ σ' : _root_.ThreeSum1960614.Machine.Light.State} {c : ℕ} (h : _root_.ThreeSum1960614.Machine.Light.Exec lim P d s σ σ' c) (R : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Exec lim (P ++ R) d s σ σ' c := by
  induction h with
  | skip => exact _root_.ThreeSum1960614.Machine.Light.Exec.skip
  | set h => exact _root_.ThreeSum1960614.Machine.Light.Exec.set h
  | store h₁ h₂ h₃ => exact _root_.ThreeSum1960614.Machine.Light.Exec.store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.call h₁ (_root_.ThreeSum1960614.Machine.Light.getElem?_append_of_eq_some h₂ R) h₃ ih

/-! ## The rules -/





/-- What is proved about a program holds for the program with more procedures appended. -/
theorem Ends.append {s σ T Q} (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ T Q) (R : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim (P ++ R) d s σ T Q := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he.append R, hc, hq⟩























/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/


















/-! ## Simplification -/

attribute [simp] _root_.ThreeSum1960614.Machine.Light.Expr.val _root_.ThreeSum1960614.Machine.Light.Expr.cost _root_.ThreeSum1960614.Machine.Light.Expr.Safe _root_.Light.Op.eval _root_.ThreeSum1960614.Machine.Light.Cond.Holds _root_.ThreeSum1960614.Machine.Light.Cond.cost _root_.ThreeSum1960614.Machine.Light.Cond.Safe _root_.Light.frame







/-! ## The limits -/









end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.Light


/-! ## Regions -/









/-! ## Memories that agree on some cells -/













variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}



theorem SameOn.refl : _root_.ThreeSum1960614.Machine.Light.SameOn K μ μ := fun _ _ => rfl









/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}















/-! ## The tactics -/











end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Specifications of procedures -/



section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}

/-- From a theorem about a body to the specification. -/
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : _root_.ThreeSum1960614.Machine.Light.Stmt}
    (hp : P[p]? = some body)
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d body ⟨_root_.Light.frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩







/-- A specification holds for the program with more procedures appended. -/
theorem Meets.append (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (P' : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim (P ++ P') p d vals μ T R := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, _root_.ThreeSum1960614.Machine.Light.getElem?_append_of_eq_some hp P', he.append P'⟩

end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List _root_.ThreeSum1960614.Machine.Light.Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} {s : _root_.ThreeSum1960614.Machine.Light.Stmt}









end

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact relocation of closed verified procedure libraries

Every procedure call is shifted by the same list offset. The structural
execution proof preserves the exact initial/final states, runtime, memory
addresses, values, and depth budget. It permits composition of independently
verified fixed programs without assuming a new implementation contract.
-/

namespace ThreeSum.ReportingHostRelocation
open _root_.ThreeSum.ReportingHostRelocation


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light





theorem lookup {P : _root_.ThreeSum1960614.Machine.Light.Program} {p : ℕ} {body : _root_.ThreeSum1960614.Machine.Light.Stmt} (h : P[p]? = some body) (prefixProgram : _root_.ThreeSum1960614.Machine.Light.Program) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program prefixProgram P)[prefixProgram.length+p]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate prefixProgram.length body) := by
  apply _root_.ThreeSum1960614.Machine.Light.getElem?_append_length_add
  rw [List.getElem?_map,h]
  rfl

theorem exec {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ σ' : _root_.ThreeSum1960614.Machine.Light.State} {c : ℕ}
    (h : _root_.ThreeSum1960614.Machine.Light.Exec lim P d s σ σ' c) (prefixProgram : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Exec lim (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program prefixProgram P) d (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate prefixProgram.length s) σ σ' c := by
  induction h with
  | skip => exact _root_.ThreeSum1960614.Machine.Light.Exec.skip
  | set h => exact _root_.ThreeSum1960614.Machine.Light.Exec.set h
  | store h₁ h₂ h₃ => exact _root_.ThreeSum1960614.Machine.Light.Exec.store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.call h₁ (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.lookup h₂ prefixProgram) h₃ ih

theorem ends {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ : _root_.ThreeSum1960614.Machine.Light.State} {T : ℕ} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ T Q) (prefixProgram : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program prefixProgram P) d (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate prefixProgram.length s) σ T Q := by
  obtain ⟨σ',c,he,hc,hq⟩ := h
  exact ⟨σ',c,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.exec he prefixProgram,hc,hq⟩

theorem meets {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {p d : ℕ} {vals : List ℤ} {μ : ℕ → ℤ}
    {T : ℕ} {R : ℤ → (ℕ → ℤ) → Prop} (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (prefixProgram : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program prefixProgram P) (prefixProgram.length+p) d vals μ T R := by
  obtain ⟨body,hbody,he⟩ := h
  exact ⟨_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate prefixProgram.length body,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.lookup hbody prefixProgram,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.ends he prefixProgram⟩

end ThreeSum.ReportingHostRelocation

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp

/-! ## Limits -/





/-- A smaller need is allowed for if a larger one is, also with a larger free pointer and at a
larger depth if the sums are not larger. -/
theorem Need.Ok.mono {r r' : _root_.ThreeSum1960614.Machine.Light.Need} {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {fr fr' d d' : ℕ} (h : r.Ok lim fr d)
    (hw : r'.word ≤ r.word) (hc : fr' + r'.cells ≤ fr + r.cells)
    (hd : d' + r'.depth ≤ d + r.depth) : r'.Ok lim fr' d' :=
  ⟨le_trans (by exact_mod_cast hw) h.word, hc.trans h.cells, h.space, hd.trans h.depth⟩



/-! ## Specifications of single routines -/



/-! ## Tasks and solvers -/





















/-! ## Hosts -/





/-! ## Tasks with a list of parameters -/











end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A complete original-input solver for the finite exceptional sizes

This four-procedure program checks every original-position triple and all
three inequalities between its indices. Its time is polynomial but is not
the target subquadratic bound. It supplies the exact fallback needed before
the asymptotic parameter regime, with no hypothesis on the integer values
beyond the task's given magnitude bound.
-/

namespace ThreeSum.LightBruteThreeSum
open _root_.ThreeSum.LightBruteThreeSum


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSumApsp.Spec
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.Spec

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000









theorem program_length : _root_.ThreeSum1960614.Machine.ThreeSum.LightBruteThreeSum.program.length=4 := rfl

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}







end ThreeSum.LightBruteThreeSum

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Affine resources for the actual finite-cutoff hybrid

The fast branch uses the computed magnitude `n^κ`; the fallback retains
the supplied magnitude `U`. Both branches reuse the same free address.
The fixed cutoff and exponent are included among the actual scalar word
controls, together with every intermediate integer power.
-/

namespace ThreeSum.ThreeSumFastResourcesHybrid
open _root_.ThreeSum.ThreeSumFastResourcesHybrid


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1700000
set_option maxRecDepth 16000











theorem brute_at_depth_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {κ cutoff n U free d e : ℕ}
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.need κ cutoff n U).Ok lim free d) (he : e≤d+2) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightBruteThreeSum.need n U).Ok lim free e :=
  H.mono (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.need]; omega) (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.need]; omega)
    (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.need]; omega)

theorem brute_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {κ cutoff n U free d : ℕ}
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.need κ cutoff n U).Ok lim free d) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightBruteThreeSum.need n U).Ok lim free (d+1) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.brute_at_depth_of_ok H (by omega)

theorem scalar_word_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {κ cutoff n U free d : ℕ}
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.need κ cutoff n U).Ok lim free d) :
    ((n+κ+cutoff+U+(n+1)^(κ+1)+10 : ℕ) : ℤ)≤lim.word := by
  have hh : n+κ+cutoff+U+(n+1)^(κ+1)+10≤(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.need κ cutoff n U).word := by
    dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.need,_root_.ThreeSum.ThreeSumFastResourcesHybrid.controls,_root_.ThreeSum1960614.Machine.ThreeSum.LightBruteThreeSum.need,_root_.ThreeSum.LightOriginalTripleRow.word]
    omega
  exact (Int.ofNat_le.mpr hh).trans H.word

theorem power_word_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {κ cutoff n U free d i : ℕ}
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.need κ cutoff n U).Ok lim free d) (hi : i≤κ) : ((n^i : ℕ) : ℤ)≤lim.word := by
  have hh : n^i≤(n+1)^(κ+1) :=
    (Nat.pow_le_pow_left (by omega : n≤n+1) i).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  exact (Int.ofNat_le.mpr (show n^i≤n+κ+cutoff+U+(n+1)^(κ+1)+10 by omega)).trans
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.scalar_word_of_ok H)

theorem outer_depth_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {κ cutoff n U free d : ℕ}
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.need κ cutoff n U).Ok lim free d) : d+2<lim.depth := by
  have hd := H.depth
  dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.need] at hd
  omega

theorem source_region_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {κ cutoff n U src free d : ℕ}
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.need κ cutoff n U).Ok lim free d) (hsrc : src+n≤free) :
    src+n≤lim.space ∧ (free : ℤ)≤lim.word := by
  have hf : free≤lim.space := by have hh := H.cells; omega
  exact ⟨hsrc.trans hf,(Int.ofNat_le.mpr hf).trans H.space⟩



end ThreeSum.ThreeSumFastResourcesHybrid

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact assembly and execution of the final hybrid caller

The supplied first537 procedures are followed by the relocated four-procedure
original-triple solver, one integer-power procedure, and the hybrid caller.
The two runtime guards use the actual size and the supplied magnitude bound.
-/

namespace ThreeSum.LightThreeSumHybridCore
open _root_.ThreeSum.LightThreeSumHybridCore


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1400000
set_option maxRecDepth 18000







theorem libraries_length {fastP : _root_.ThreeSum1960614.Machine.Light.Program} (hlen : fastP.length=537) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.libraries fastP).length=541 := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.libraries,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program,List.length_append,
    List.length_map,hlen,_root_.ThreeSum1960614.Machine.ThreeSum.LightBruteThreeSum.program_length]



theorem main_lookup {fastP : _root_.ThreeSum1960614.Machine.Light.Program} (hlen : fastP.length=537) (κ cutoff : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.program fastP κ cutoff)[542]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.body κ cutoff) := by
  have hh : (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.libraries fastP++[_root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.body,_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.body κ cutoff])[(_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.libraries fastP).length+1]?=
      some (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.body κ cutoff) := by
    apply _root_.ThreeSum1960614.Machine.Light.getElem?_append_length_add
    rfl
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.program,_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.libraries_length hlen] using hh

theorem power_lookup {fastP : _root_.ThreeSum1960614.Machine.Light.Program} (hlen : fastP.length=537) (κ cutoff : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.program fastP κ cutoff)[541]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.body := by
  have hh : (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.libraries fastP++[_root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.body,_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.body κ cutoff])[(_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.libraries fastP).length+0]?=
      some _root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.body := by
    apply _root_.ThreeSum1960614.Machine.Light.getElem?_append_length_add
    rfl
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.program,_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.libraries_length hlen] using hh

theorem brute_meets {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {fastP : _root_.ThreeSum1960614.Machine.Light.Program} {κ cutoff src n U free d : ℕ}
    (hlen : fastP.length=537) (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (hn : 0<n) (hsrc : src+n≤free) (H : (_root_.ThreeSum1960614.Machine.ThreeSum.LightBruteThreeSum.need n U).Ok lim free d)
    (hread : ∀ i : Fin n, μ (src+i.val)=x i) (hx : ∀ i, |x i|≤(U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.program fastP κ cutoff) 540 d [n,U,src,free] μ (_root_.ThreeSum.LightBruteThreeSum.time n)
      (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ _root_.ThreeSum.Coloring.DistinctZeroSum x) ∧ ν=μ) := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightBruteThreeSum.meets (P := _root_.ThreeSum1960614.Machine.ThreeSum.LightBruteThreeSum.program) (pMain := 3)
    (pScan := 2) (pRow := 0) (pDivide := 1) x μ rfl rfl rfl rfl hn hsrc H hread hx
  have hrun := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.meets hh fastP).append
    [_root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.body,_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.body κ cutoff]
  rw [hlen] at hrun
  exact hrun



end ThreeSum.LightThreeSumHybridCore

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
section

/-- The branch law is consumed only after both runtime guards succeed. The
    final concrete module discharges it using the verified fast executable. -/
theorem ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.program_meets__implementation_b60e12661b {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {fastP : _root_.ThreeSum1960614.Machine.Light.Program} {κ cutoff src n U free d : ℕ}
    (hlen : fastP.length=537) (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (hn : 0<n) (hsrc : src+n≤free)
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.need κ cutoff n U).Ok lim free d)
    (hread : ∀ i : Fin n, μ (src+i.val)=x i) (hx : ∀ i, |x i|≤(U : ℤ))
    (hfast : cutoff≤n → U≤n^κ →
      _root_.ThreeSum1960614.Machine.Light.Meets lim fastP 536 (d+1) [src,n,free] μ
        (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.time (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.colorBudget κ n) n)
        (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ _root_.ThreeSum.Coloring.DistinctZeroSum x) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν free)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.program fastP κ cutoff) 542 d [n,U,src,free] μ
      (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.time κ cutoff n U)
      (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ _root_.ThreeSum.Coloring.DistinctZeroSum x) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) := by
  have hw := H.space
  have hword := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.scalar_word_of_ok H
  have hd := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.outer_depth_of_ok H
  have hregions := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.source_region_of_ok H hsrc
  have hspace := hregions.1
  have hfreeWord := hregions.2
  have hκWord : (κ : ℤ)≤lim.word := by omega
  have hpowerWord := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.power_word_of_ok H (i := κ) le_rfl
  have hpowerCast : ((n^κ : ℕ) : ℤ)=(n : ℤ)^κ := Nat.cast_pow n κ
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.brute_meets (κ := κ) (cutoff := cutoff) hlen x μ hn hsrc
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.brute_of_ok H) hread hx
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.meets (d := d+1) (b := n) (e := κ)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.power_lookup hlen κ cutoff) μ hκWord
    (fun i hi => _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.power_word_of_ok H hi)
  by_cases hsmall : n<cutoff
  · rw [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.time,if_pos (Or.inl hsmall)]
    apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.main_lookup hlen κ cutoff)
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.body
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.iteIffThen (n < cutoff) (fun hyes => ?_) (fun hno => ?_) ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
       all_goals
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
    · (focus
         ((first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
         first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hb _ (by omega)) ?_ ?_ ?_ ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hb ?_ ?_ ?_ ?_
         on_goal -1 =>
           first
           | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [] <;>
                 first
                 | omega
                 | (ring_nf; omega))
         on_goal -1 => omega
         on_goal -1 =>
           ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
             (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
             simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
         on_goal -1 => (rintro r ν ⟨hbool, hcorrect, hmem⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
      subst ν
      exact ⟨hbool,hcorrect,_root_.ThreeSum1960614.Machine.Light.SameOn.refl⟩
    · omega
  · by_cases hlarge : n^κ<U
    · rw [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.time,if_pos (Or.inr hlarge)]
      apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.main_lookup hlen κ cutoff)
      unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.body
      (focus
         ((first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
         refine _root_.ThreeSum1960614.Machine.Light.Ends.iteIffThen (n < cutoff) (fun hyes => ?_) (fun hno => ?_) ?_ ?_
         on_goal -1 =>
           first
           | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [] <;>
                 first
                 | omega
                 | (ring_nf; omega))
         on_goal -1 =>
           ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
             (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
             simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
         all_goals
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
      · omega
      · (focus
           ((first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
             repeat
               with_unfolding_none
                 first
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hp _ (by omega)) ?_ ?_ ?_ ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hp ?_ ?_ ?_ ?_
           on_goal -1 =>
             first
             | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega))
           on_goal -1 => omega
           on_goal -1 =>
             ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
               (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
               simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
           on_goal -1 => (rintro power ν ⟨hpower, hmem⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
        subst ν
        subst power
        (focus
           ((first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
             repeat
               with_unfolding_none
                 first
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
           refine _root_.ThreeSum1960614.Machine.Light.Ends.iteIffThen (n ^ κ < U) (fun hyesU => ?_) (fun hnoU => ?_) ?_ ?_
           on_goal -1 =>
             first
             | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega))
           on_goal -1 =>
             ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
               (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
               simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
           all_goals
             repeat
               with_unfolding_none
                 first
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
        · (focus
             ((first
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
               repeat
                 with_unfolding_none
                   first
                   | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                   | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hb _ (by omega)) ?_ ?_ ?_ ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hb ?_ ?_ ?_ ?_
             on_goal -1 =>
               first
               | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [] <;>
                     first
                     | omega
                     | (ring_nf; omega))
             on_goal -1 => omega
             on_goal -1 =>
               ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                 (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                 simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
             on_goal -1 => (rintro r ξ ⟨hbool, hcorrect, hmem⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
          subst ξ
          exact ⟨hbool,hcorrect,_root_.ThreeSum1960614.Machine.Light.SameOn.refl⟩
        · omega
    · rw [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.time,if_neg (not_or_intro hsmall hlarge)]
      have hf := (hfast (by omega) (by omega)).append
        (_root_.ThreeSum1960614.Machine.ThreeSum.LightBruteThreeSum.program.map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate fastP.length)++
          [_root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.body,_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.body κ cutoff])
      have hf' : _root_.ThreeSum1960614.Machine.Light.Meets lim (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.program fastP κ cutoff) 536 (d+1) [src,n,free] μ
          (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.time (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.colorBudget κ n) n)
          (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ _root_.ThreeSum.Coloring.DistinctZeroSum x) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) := by
        simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.program,_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.libraries,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program,List.append_assoc] using hf
      apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.main_lookup hlen κ cutoff)
      unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.body
      (focus
         ((first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
         refine _root_.ThreeSum1960614.Machine.Light.Ends.iteIffThen (n < cutoff) (fun hyes => ?_) (fun hno => ?_) ?_ ?_
         on_goal -1 =>
           first
           | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [] <;>
                 first
                 | omega
                 | (ring_nf; omega))
         on_goal -1 =>
           ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
             (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
             simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
         all_goals
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
      · omega
      · (focus
           ((first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
             repeat
               with_unfolding_none
                 first
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hp _ (by omega)) ?_ ?_ ?_ ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hp ?_ ?_ ?_ ?_
           on_goal -1 =>
             first
             | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega))
           on_goal -1 => omega
           on_goal -1 =>
             ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
               (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
               simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
           on_goal -1 => (rintro power ν ⟨hpower, hmem⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
        subst ν
        subst power
        (focus
           ((first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
             repeat
               with_unfolding_none
                 first
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
           refine _root_.ThreeSum1960614.Machine.Light.Ends.iteIffThen (n ^ κ < U) (fun hyesU => ?_) (fun hnoU => ?_) ?_ ?_
           on_goal -1 =>
             first
             | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [] <;>
                   first
                   | omega
                   | (ring_nf; omega))
           on_goal -1 =>
             ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
               (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
               simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
           all_goals
             repeat
               with_unfolding_none
                 first
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
        · omega
        · (focus
             ((first
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
               repeat
                 with_unfolding_none
                   first
                   | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                   | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hf' _ (by omega)) ?_ ?_ ?_ ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hf' ?_ ?_ ?_ ?_
             on_goal -1 =>
               first
               | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [] <;>
                     first
                     | omega
                     | (ring_nf; omega))
             on_goal -1 => omega
             on_goal -1 =>
               ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                 (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                 simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
             on_goal -1 => (rintro r ξ hh; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
          exact hh
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.program_meets__implementation_b60e12661b) := (@ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.program_meets__implementation_b60e12661b)

#print axioms solution
