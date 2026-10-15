-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBandPrimeMinimum.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:45:06.522694+00:00
-- url     : https://prove2.me/submissions/d6ed57bd-0a17-4cd5-998d-9b81f695bde7

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
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
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
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
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandWeightedScore_program_meets
import Theorems.Thm_ThreeSum_BandWeightedScore_block_bound

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPrimeChoice
end ThreeSum.BandPrimeChoice
namespace ThreeSum.BandWeightedScore
end ThreeSum.BandWeightedScore
namespace ThreeSum.LightBandPrimeMinimum
end ThreeSum.LightBandPrimeMinimum
namespace ThreeSum.LightMinimum
end ThreeSum.LightMinimum
namespace ThreeSum.LightPrimeMinimum
end ThreeSum.LightPrimeMinimum
namespace ThreeSum.WeightedScore
end ThreeSum.WeightedScore
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BandEnumeration
end ThreeSum1960614.Machine.ThreeSum.BandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice
end ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice
namespace ThreeSum1960614.Machine.ThreeSum.BandWeightedScore
end ThreeSum1960614.Machine.ThreeSum.BandWeightedScore
namespace ThreeSum1960614.Machine.ThreeSum.LightBandPrimeMinimum
end ThreeSum1960614.Machine.ThreeSum.LightBandPrimeMinimum
namespace ThreeSum1960614.Machine.ThreeSum.LightMinimum
end ThreeSum1960614.Machine.ThreeSum.LightMinimum
namespace ThreeSum1960614.Machine.ThreeSum.LightPrimeMinimum
end ThreeSum1960614.Machine.ThreeSum.LightPrimeMinimum
namespace ThreeSum1960614.Machine.ThreeSum.WeightedScore
end ThreeSum1960614.Machine.ThreeSum.WeightedScore
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

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









theorem Ends.ite {σ T c s₁ s₂} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} (T' : ℕ) (hs : c.Safe lim σ)
    (h₁ : c.Holds σ → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₁ σ T' Q) (h₂ : ¬ c.Holds σ → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₂ σ T' Q)
    (hT : c.cost + 1 + T' ≤ T) : _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.ite c s₁ s₂) σ T Q := by
  by_cases hv : c.Holds σ
  · obtain ⟨σ', k, he, hk, hq⟩ := h₁ hv
    exact ⟨σ', _, _root_.ThreeSum1960614.Machine.Light.Exec.iteTrue hs hv he, by omega, hq⟩
  · obtain ⟨σ', k, he, hk, hq⟩ := h₂ hv
    exact ⟨σ', _, _root_.ThreeSum1960614.Machine.Light.Exec.iteFalse hs hv he, by omega, hq⟩













/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/


















/-! ## Simplification -/

attribute [simp] _root_.ThreeSum1960614.Machine.Light.Expr.val _root_.ThreeSum1960614.Machine.Light.Expr.cost _root_.ThreeSum1960614.Machine.Light.Expr.Safe _root_.Light.Op.eval _root_.ThreeSum1960614.Machine.Light.Cond.Holds _root_.ThreeSum1960614.Machine.Light.Cond.cost _root_.ThreeSum1960614.Machine.Light.Cond.Safe _root_.Light.frame





/-- The natural number behind an address that is a sum of two natural numbers. -/
@[simp] theorem toNat_natCast_add_natCast (a b : ℕ) : ((a : ℤ) + (b : ℤ)).toNat = a + b := by
  rw [← Nat.cast_add, Int.toNat_natCast]

/-! ## The limits -/









end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp





variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}

























/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : _root_.ThreeSum1960614.Machine.Light.Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]





















































end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Blocks -/











/-! ## The default proofs -/











/-! ## Rules for blocks -/













/-! ## Sequencing: what is left of the time goes to the rest of the program -/























/-- A branch at the end of the program: both sides get the steps that the test leaves. -/
theorem Ends.iteLast {σ : _root_.ThreeSum1960614.Machine.Light.State} {T : ℕ} {c : _root_.ThreeSum1960614.Machine.Light.Cond} {s₁ s₂ : _root_.ThreeSum1960614.Machine.Light.Stmt} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}
    (h₁ : c.Holds σ → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₁ σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₂ σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))) (hT : c.cost + 1 ≤ T := by (first
                                                                     | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                         first
                                                                         | omega
                                                                         | (ring_nf; omega))
                                                                     | omega
                                                                     |
                                                                       (simp [] <;>
                                                                           first
                                                                           | omega
                                                                           | (ring_nf; omega)))) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.ite c s₁ s₂) σ T Q :=
  _root_.ThreeSum1960614.Machine.Light.Ends.ite _ hs h₁ h₂ (by omega)





/-! ## Loops whose body is a block -/



/-! ## Counting loops -/







end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## The list of the locals -/







/-- Zeros at the end of the list do not matter. -/
theorem frame_append_zeros (l : List ℤ) (n : ℕ) : _root_.Light.frame (l ++ List.replicate n 0) = _root_.Light.frame l := by
  funext y
  simp only [_root_.Light.frame, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split_ifs with h1 h2
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega)]

/-! ## The value of an expression -/



/-! ## One statement -/

section rules

variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}

















end rules

/-! ## Locals by name, and locals whose values do not matter -/























section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}







/-! ## A piece of program text with a lemma of its own -/

variable {T T₁ : ℕ} {s s₁ s₂ : _root_.ThreeSum1960614.Machine.Light.Stmt} {Q R : _root_.ThreeSum1960614.Machine.Light.State → Prop}







/-! ## Counting loops with scratch variables -/



end

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

/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩





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
# The exact physical band-owner record order

There is one four-cell record for every owner-table cell, in BC, AB, AC
rectangle order. A zero flag is a lookup miss. Successful records retain
their physical owner slot even when several owners produce the same triple.
-/

namespace ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandCandidateRows


open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000































theorem cells_length (rs : List _root_.ThreeSum.BandCandidateRows.Record) : (_root_.ThreeSum.BandCandidateRows.cells rs).length=4*rs.length := by
  induction rs with
  | nil => simp [_root_.ThreeSum.BandCandidateRows.cells]
  | cons r rs ih => simp only [_root_.ThreeSum.BandCandidateRows.cells,List.flatMap_cons,List.length_append,_root_.ThreeSum.BandCandidateRows.Record.cells,
      List.length_cons,List.length_nil] at *; omega























end ThreeSum.BandCandidateRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A finite array minimum scan in the benchmark language

The selected index is a deterministic left-to-right minimum. Its value
can therefore instantiate the exact mean bound for offset balancing.
-/

namespace ThreeSum.LightMinimum
open _root_.ThreeSum.LightMinimum


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light



theorem least_lt (f : ℕ → ℤ) {n : ℕ} (hn : 0 < n) : _root_.ThreeSum.LightMinimum.least f n < n := by
  induction n with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero => simp [_root_.ThreeSum.LightMinimum.least]
      | succ n =>
          have h := ih (by omega)
          unfold _root_.ThreeSum.LightMinimum.least
          split <;> omega

theorem least_lt_of_le (f : ℕ → ℤ) {j n : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    _root_.ThreeSum.LightMinimum.least f j < n := by
  by_cases h : j = 0
  · simp [h, _root_.ThreeSum.LightMinimum.least, hn]
  · exact (_root_.ThreeSum1960614.Machine.ThreeSum.LightMinimum.least_lt f (by omega)).trans_le hj









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



end ThreeSum.LightMinimum

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Executing deterministic prime-score minimization

The same finite prime array supplies the candidate multipliers and the
auxiliary tests. The program streams exact scores at `q * primes i`, retaining
the first minimum. All weighted-score calls reuse one scratch region.
-/

namespace ThreeSum.LightPrimeMinimum
open _root_.ThreeSum.LightPrimeMinimum


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.WeightedScore
open _root_.ThreeSum1960614.Machine.ThreeSum.WeightedScore

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000











theorem score_congr {primes : ℕ → ℕ} {s q nA nB nC : ℕ} {A A' B B' C C' : ℕ → ℤ}
    (ha : ∀ i < nA, A i = A' i) (hb : ∀ i < nB, B i = B' i)
    (hc : ∀ i < nC, C i = C' i) :
    _root_.ThreeSum.WeightedScore.score primes s q nA nB nC A B C = _root_.ThreeSum.WeightedScore.score primes s q nA nB nC A' B' C' := by
  unfold _root_.ThreeSum.WeightedScore.score _root_.ThreeSum.Arithmetic.weightedFalseCount
  apply Finset.sum_congr rfl
  intro t ht
  simp only [_root_.ThreeSum.ModuloCounts.triples, Finset.mem_product, Finset.mem_range] at ht
  simp only [_root_.ThreeSum.ModuloCounts.difference, ha _ ht.1, hb _ ht.2.1, hc _ ht.2.2]
  rfl











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}













end ThreeSum.LightPrimeMinimum

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The aggregate weighted score of physical band-owner candidates

Each flagged owner contributes the score of its three actual truncated
bands. Owner multiplicities are retained. The contraction and initial bound
therefore apply to the same quadratic catalog that the program scans.
-/

namespace ThreeSum.BandWeightedScore
open _root_.ThreeSum.BandWeightedScore


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000







theorem position_lt {n g a i : ℕ} (hi : i < _root_.ThreeSum.BandWeightedScore.length n g a) : a*g+i < n := by
  have hh := min_le_right g (n-a*g)
  unfold _root_.ThreeSum.BandWeightedScore.length at hi
  omega















theorem partialScore_bound (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (k : ℕ)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j) :
    _root_.ThreeSum.BandWeightedScore.partialScore primes s q nA nB nC g A B C rs k ≤ k*(s*g^3) := by
  calc
    _ ≤ ∑ _i ∈ range k, s*g^3 := sum_le_sum fun i _ => _root_.ThreeSum.BandWeightedScore.block_bound primes s q nA nB nC g A B C _ hprime hinj
    _ = _ := by simp

theorem score_bound (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j) :
    _root_.ThreeSum.BandWeightedScore.score primes s q nA nB nC g A B C rs ≤ rs.length*(s*g^3) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.partialScore_bound primes s q nA nB nC g A B C rs rs.length hprime hinj

theorem block_congr {primes : ℕ → ℕ} {s q nA nB nC g : ℕ}
    {A A' B B' C C' : ℕ → ℤ} (r : _root_.ThreeSum.BandCandidateRows.Record)
    (hA : ∀ i < nA, A i=A' i) (hB : ∀ i < nB, B i=B' i) (hC : ∀ i < nC, C i=C' i) :
    _root_.ThreeSum.BandWeightedScore.block primes s q nA nB nC g A B C r=_root_.ThreeSum.BandWeightedScore.block primes s q nA nB nC g A' B' C' r := by
  unfold _root_.ThreeSum.BandWeightedScore.block
  split_ifs
  · exact _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimeMinimum.score_congr
      (fun i hi => hA _ (_root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.position_lt hi)) (fun i hi => hB _ (_root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.position_lt hi))
      (fun i hi => hC _ (_root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.position_lt hi))
  · rfl

theorem score_congr {primes : ℕ → ℕ} {s q nA nB nC g : ℕ}
    {A A' B B' C C' : ℕ → ℤ} (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (hA : ∀ i < nA, A i=A' i) (hB : ∀ i < nB, B i=B' i) (hC : ∀ i < nC, C i=C' i) :
    _root_.ThreeSum.BandWeightedScore.score primes s q nA nB nC g A B C rs=_root_.ThreeSum.BandWeightedScore.score primes s q nA nB nC g A' B' C' rs := by
  unfold _root_.ThreeSum.BandWeightedScore.score _root_.ThreeSum.BandWeightedScore.partialScore
  exact sum_congr rfl fun i _ => _root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.block_congr (rs.getD i default) hA hB hC





end ThreeSum.BandWeightedScore

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Execute common-prime minimization over all owner candidates

Every candidate prime is scored by the actual aggregate band loop. The
first minimum is returned, with no supplied score array or counting oracle.
-/

namespace ThreeSum.LightBandPrimeMinimum
open _root_.ThreeSum.LightBandPrimeMinimum


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandWeightedScore
open _root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore
open _root_.ThreeSum.BandPrimeChoice
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000











theorem maxMod_le_word (maxMod nA nB nC g R s U : ℕ) :
    maxMod ≤ _root_.ThreeSum.LightBandWeightedScore.word maxMod nA nB nC g R s U := by
  unfold _root_.ThreeSum.LightBandWeightedScore.word _root_.ThreeSum.LightBandWeightedScoreCell.word _root_.ThreeSum.LightWeightedScore.word
  omega

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs q aux s free maxMod U : ℕ}



end ThreeSum.LightBandPrimeMinimum

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBandPrimeMinimum
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeMinimum

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandWeightedScore
open _root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore
open _root_.ThreeSum.BandPrimeChoice
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs q aux s free maxMod U : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightBandPrimeMinimum.program_meets__implementation_a74620a2b6 (primes : ℕ → ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+Nat.clog 2 maxMod+7 ≤ lim.depth)
    (hg : 0 < g) (hq : 0 < q) (hs : 0 < s)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hrecs : recs+4*rs.length ≤ free) (haux : aux+s ≤ free)
    (hspace : _root_.ThreeSum.LightWeightedScore.space free maxMod g U ≤ lim.space)
    (hword : (_root_.ThreeSum.LightBandWeightedScore.word maxMod nA nB nC g rs.length s U : ℤ) ≤ lim.word)
    (hrecords : _root_.ThreeSum1960614.Machine.Light.Seg μ recs (_root_.ThreeSum.BandCandidateRows.cells rs))
    (hflag : ∀ r ∈ rs, r.flag=0 ∨ r.flag=1)
    (hvalid : ∀ r ∈ rs, r.flag=1 → r.a*g ≤ nA ∧ r.b*g ≤ nB ∧ r.c*g ≤ nC)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux+i)=(primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hproduct : ∀ i < s, ∀ j < s, q*primes i*primes j ≤ maxMod) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeMinimum.program 17 d [a,b,c,nA,nB,nC,g,recs,rs.length,q,aux,s,free] μ
      (_root_.ThreeSum.LightBandPrimeMinimum.time maxMod g rs.length s U)
      (fun result ν => result=(_root_.ThreeSum.BandPrimeChoice.chosenPrime primes s q nA nB nC g
        (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) rs : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) := by
  let A := fun i => μ (a+i)
  let B := fun i => μ (b+i)
  let C := fun i => μ (c+i)
  let f := _root_.ThreeSum.BandPrimeChoice.candidateScore primes s q nA nB nC g A B C rs
  let ct := _root_.ThreeSum.LightBandWeightedScore.time maxMod g rs.length s U
  have htotal : rs.length*(s*g^3) ≤ _root_.ThreeSum.LightBandWeightedScore.word maxMod nA nB nC g rs.length s U := by
    unfold _root_.ThreeSum.LightBandWeightedScore.word
    omega
  have htotalWord : ((rs.length*(s*g^3) : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr htotal).trans hword
  have hf (i : ℕ) : 0 ≤ f i ∧ f i ≤ lim.word := by
    constructor
    · exact Int.natCast_nonneg _
    · exact (Int.ofNat_le.mpr (_root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.score_bound primes s (q*primes i) nA nB nC g A B C rs hprime hinj)).trans htotalWord
  have hmaxWord : (maxMod : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeMinimum.maxMod_le_word maxMod nA nB nC g rs.length s U)).trans hword
  have hqiMax (i : ℕ) (hi : i < s) : q*primes i ≤ maxMod :=
    (Nat.le_mul_of_pos_right _ (hprime 0 hs).pos).trans (hproduct i hi 0 hs)
  have hpiWord (i : ℕ) (hi : i < s) : (primes i : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ((Nat.le_mul_of_pos_left (primes i) hq).trans (hqiMax i hi))).trans hmaxWord
  have hqiWord (i : ℕ) (hi : i < s) : (q : ℤ)*(primes i : ℤ) ≤ lim.word := by
    exact_mod_cast (Int.ofNat_le.mpr (hqiMax i hi)).trans hmaxWord
  have hfree : free ≤ lim.space := by
    have hh := (le_max_right _ _).trans hspace
    change free+(Nat.log 2 (maxMod+1)+2) ≤ lim.space at hh
    omega
  have hcall (ν : ℕ → ℤ) (i : ℕ) (hi : i < s) (hkeep : _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) :
      _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeMinimum.program 16 (d+1) [a,b,c,nA,nB,nC,g,recs,rs.length,q*primes i,aux,s,free] ν ct
        (fun value ξ => value=f i ∧ _root_.ThreeSum1960614.Machine.Light.Kept ν ξ free) := by
    have hrecordsν : _root_.ThreeSum1960614.Machine.Light.Seg ν recs (_root_.ThreeSum.BandCandidateRows.cells rs) := by
      apply hrecords.congr
      intro j hj
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.cells_length] at hj
      exact hkeep _ (by omega)
    have hAν : ∀ j < nA, |ν (a+j)| ≤ (U : ℤ) := by
      intro j hj; rw [hkeep _ (by omega)]; exact hA j hj
    have hBν : ∀ j < nB, |ν (b+j)| ≤ (U : ℤ) := by
      intro j hj; rw [hkeep _ (by omega)]; exact hB j hj
    have hCν : ∀ j < nC, |ν (c+j)| ≤ (U : ℤ) := by
      intro j hj; rw [hkeep _ (by omega)]; exact hC j hj
    have hreadν : ∀ j < s, ν (aux+j)=(primes j : ℤ) := by
      intro j hj; rw [hkeep _ (by omega)]; exact hread j hj
    refine ((_root_.ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScore.program_meets (d := d+1) (μ := ν) primes rs hw (by omega)
      hg (Nat.mul_pos hq (hprime i hi).pos) (hqiMax i hi) ha hb hc hrecs haux hspace hword
      hrecordsν hflag hvalid hAν hBν hCν hreadν hprime hinj (hproduct i hi)).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeMinimum.body 16]).mono le_rfl ?_
    rintro value ξ ⟨hvalue,hkeep'⟩
    refine ⟨hvalue.trans ?_,hkeep'⟩
    unfold f _root_.ThreeSum.BandPrimeChoice.candidateScore
    congr 1
    exact _root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.score_congr rs (fun j hj => hkeep _ (by omega))
      (fun j hj => hkeep _ (by omega)) (fun j hj => hkeep _ (by omega))
  have hp0 := hpiWord 0 hs
  have hq0 := hqiWord 0 hs
  have hq0Nonneg : (0 : ℤ) ≤ (q : ℤ)*(primes 0 : ℤ) := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hread0 : μ aux=(primes 0 : ℤ) := by simpa only [Nat.add_zero] using hread 0 hs
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 17) (by rfl : program[17]?=some (body 16))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeMinimum.body _root_.ThreeSum.LightBandPrimeMinimum.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     first
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((hcall μ 0 hs (fun _ _ => rfl)) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcall μ 0 hs (fun _ _ => rfl)) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hread0, ct]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hread0, ct] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread0, ct] <;> omega)
     on_goal -1 => (rintro value μ₁ ⟨hvalue, hkeep₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst value
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
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
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine _root_.ThreeSum1960614.Machine.Light.Ends.pieceThen (_root_.ThreeSum1960614.Machine.Light.Ends.for (T := s*(ct+140)+30)
    (Q := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeMinimum.Inv μ f a b c nA nB nC g recs rs.length q aux s free s)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeMinimum.Inv μ f a b c nA nB nC g recs rs.length q aux s free) s (ct+110)
    ?start ?round ?done ?bound (hT := by (first
                                          | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ct]
                                              first
                                              | omega
                                              | (ring_nf; omega))
                                          | omega
                                          |
                                            (simp [ct] <;>
                                                first
                                                | omega
                                                | (ring_nf; omega))))) ?finish (hT := by (first
                                                                              | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ct]
                                                                                  first
                                                                                  | omega
                                                                                  | (ring_nf; omega))
                                                                              | omega
                                                                              |
                                                                                (simp [ct] <;>
                                                                                    first
                                                                                    | omega
                                                                                    | (ring_nf; omega))))
  case start =>
    refine ⟨0,μ₁,?_,hkeep₁⟩
    simp only [_root_.ThreeSum.LightMinimum.least,_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
    exact congrArg (fun loc => (⟨loc,μ₁⟩ : _root_.ThreeSum1960614.Machine.Light.State)) (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros _ 1).symm
  case round =>
    rintro i _ hi _ ⟨old,ν,rfl,hkeep⟩
    have hbest : _root_.ThreeSum.LightMinimum.least f i < s := _root_.ThreeSum1960614.Machine.ThreeSum.LightMinimum.least_lt_of_le f hs (by omega)
    have hpi := hpiWord i hi
    have hqi := hqiWord i hi
    have hqiNonneg : (0 : ℤ) ≤ (q : ℤ)*(primes i : ℤ) := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    have hreadν : ν (aux+i)=(primes i : ℤ) := (hkeep _ (by omega)).trans (hread i hi)
    have hfi := hf i
    have hfb := hf (_root_.ThreeSum.LightMinimum.least f i)
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       first
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((hcall ν i hi hkeep) _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcall ν i hi hkeep) ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadν, ct]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hreadν, ct] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadν, ct] <;> omega)
       on_goal -1 => (rintro value ξ ⟨hvalue, hkeep'⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    subst value
    have hkept : _root_.ThreeSum1960614.Machine.Light.Kept μ ξ free := fun j hj => (hkeep' j hj).trans (hkeep j hj)
    refine _root_.ThreeSum1960614.Machine.Light.Ends.iteLast (fun hcmp => ?_) (fun hcmp => ?_) (by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
    · have hcmp' : f i < f (_root_.ThreeSum.LightMinimum.least f i) := by simpa using hcmp
      (focus
         ((first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
         refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (f i) ?_ ?_ ?_
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
         try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
      (focus
         ((first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
         refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (i : ℕ) ?_ ?_ ?_
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
         try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
      refine ⟨by simp,f i,ξ,?_,hkept⟩
      simp [_root_.ThreeSum.LightMinimum.least,hcmp',_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
    · have hcmp' : ¬ f i < f (_root_.ThreeSum.LightMinimum.least f i) := by simpa using hcmp
      apply _root_.ThreeSum1960614.Machine.Light.Ends.skip
      refine ⟨by simp,f i,ξ,?_,hkept⟩
      simp [_root_.ThreeSum.LightMinimum.least,hcmp',_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
  case done =>
    intro σ _ H
    exact H
  case bound =>
    rintro i _ hi _ ⟨old,ν,rfl,hkeep⟩
    simp
  case finish =>
    rintro _ ⟨old,ν,rfl,hkeep⟩
    have hbest : _root_.ThreeSum.LightMinimum.least f s < s := _root_.ThreeSum1960614.Machine.ThreeSum.LightMinimum.least_lt f hs
    have hbestWord := hpiWord (_root_.ThreeSum.LightMinimum.least f s) hbest
    have hreadBest : ν (aux+_root_.ThreeSum.LightMinimum.least f s)=(primes (_root_.ThreeSum.LightMinimum.least f s) : ℤ) :=
      (hkeep _ (by omega)).trans (hread _ hbest)
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (primes (_root_.ThreeSum.LightMinimum.least f s) : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadBest, ct]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hreadBest, ct] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadBest, ct] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    exact ⟨by simp [_root_.ThreeSum.BandPrimeChoice.chosenPrime,_root_.ThreeSum.BandPrimeChoice.chosenIndex,f,A,B,C],hkeep⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBandPrimeMinimum.program_meets__implementation_a74620a2b6) := (@ThreeSum1960614.Machine.ThreeSum.LightBandPrimeMinimum.program_meets__implementation_a74620a2b6)

#print axioms solution
