-- Prove2me | solution 1 for ThreeSum.LightReportingWantedRecordCall.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:09:18.375006+00:00
-- url     : https://prove2.me/submissions/708d3de6-60a2-4e2e-8a2f-a1fc5edbf4a9

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle17
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
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
import Mathlib.Algebra.Order.Field.Basic
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.Data.Int.Cast.Lemmas
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
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async true
namespace Light
end Light
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.ReportingHostWantedControls
end ThreeSum.ReportingHostWantedControls
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout

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







theorem Ends.seq {σ T s₁ s₂} {Q : State → Prop} (T₁ T₂ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' T₂ Q) (hT : T₁ + T₂ ≤ T) :
    Ends lim P d (.seq s₁ s₂) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, .seq he₁ he₂, by omega, hq⟩

























































































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























/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}














































/-! ## The tactics -/











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















































/-! ## Sequencing: what is left of the time goes to the rest of the program -/

/-- The first statement gets T₁ steps, the rest of the program what is left of T. -/
theorem Ends.next {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop} (T₁ : ℕ)
    (h : Ends lim P d s₁ σ T₁ fun σ' => Ends lim P d s₂ σ' (T - T₁) Q)
    (hT : T₁ ≤ T := by first
                           |
                             ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                   List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                               (first
                                 | ((clear * -); (omega))
                                 | omega
                                 | ((ring_nf); (omega))))
                           | omega
                           |
                             (simp [] <;>
                                 first
                                 | ((clear * -); (omega))
                                 | omega
                                 | ((ring_nf); (omega)))) : Ends lim P d (s₁ ;; s₂) σ T Q :=
  Ends.seq T₁ (T - T₁) h (by omega)

/-- Brackets do not matter: a piece of several statements, followed by the rest of the program, is
run statement by statement. -/
theorem Ends.seqAssoc {σ : State} {T : ℕ} {s₁ s₂ s₃ : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s₁ ;; (s₂ ;; s₃)) σ T Q) : Ends lim P d ((s₁ ;; s₂) ;; s₃) σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂₃ =>
    cases he₂₃ with
    | seq he₂ he₃ => exact ⟨σ', _, .seq (.seq he₁ he₂) he₃, by omega, hq⟩

/-- A `skip` before the rest of the program takes no step. -/
theorem Ends.skipThen {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop} (h : Ends lim P d s σ T Q) :
    Ends lim P d (.skip ;; s) σ T Q :=
  Ends.seq 0 T (Ends.skip h) (by omega)

/-- A `skip` may be put behind a statement. -/
theorem Ends.skipLast {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s ;; .skip) σ T Q) : Ends lim P d s σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂ =>
    cases he₂
    exact ⟨σ', _, he₁, by omega, hq⟩

/-- A program that is defined as a sequence may be treated as the sequence. -/
theorem Ends.seqSelf {σ : State} {T : ℕ} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h : Ends lim P d (s₁ ;; s₂) σ T Q) : Ends lim P d (s₁ ;; s₂) σ T Q :=
  h












































































/-! ## Loops whose body is a block -/














/-! ## Counting loops -/











































































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
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;>
                                                      first
                                                      | assumption
                                                      |
                                                        ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0 hv1 hv2
                                                              hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15 hv16
                                                              hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10 hw11
                                                              hw12 hw13);
                                                          (omega))
                                                      | omega)))
    (hT : e.cost + 1 ≤ T := by first
                                 |
                                   ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                         List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                     (first
                                       | ((clear * -); (omega))
                                       | omega
                                       | ((ring_nf); (omega))))
                                 | omega
                                 |
                                   (simp [] <;>
                                       first
                                       | ((clear * -); (omega))
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
                                                  (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;>
                                                      first
                                                      | assumption
                                                      |
                                                        ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0 hv1 hv2
                                                              hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15 hv16
                                                              hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10 hw11
                                                              hw12 hw13);
                                                          (omega))
                                                      | omega)))
    (hT : e.cost + 1 ≤ T := by first
                                 |
                                   ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                         List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                     (first
                                       | ((clear * -); (omega))
                                       | omega
                                       | ((ring_nf); (omega))))
                                 | omega
                                 |
                                   (simp [] <;>
                                       first
                                       | ((clear * -); (omega))
                                       | omega
                                       | ((ring_nf); (omega)))) :
    Ends lim P d (.set x e ;; s) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.setTo z h he le_rfl) hT



















































































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
                                                                                                        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;>
                                                                                                            first
                                                                                                            | assumption
                                                                                                            |
                                                                                                              ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0 hv1 hv2
                                                                                                                    hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15 hv16
                                                                                                                    hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10 hw11
                                                                                                                    hw12 hw13);
                                                                                                                (omega))
                                                                                                            | omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | ((clear * -); (omega))
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | ((clear * -); (omega))
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
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;>
            first
            | assumption
            |
              ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0 hv1 hv2
                    hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15 hv16
                    hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10 hw11
                    hw12 hw13);
                (omega))
            | omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | ((clear * -); (omega))
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | ((clear * -); (omega))
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
        (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;>
            first
            | assumption
            |
              ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0 hv1 hv2
                    hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15 hv16
                    hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10 hw11
                    hw12 hw13);
                (omega))
            | omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T := by first
                                                        |
                                                          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                                                                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
                                                            (first
                                                              | ((clear * -); (omega))
                                                              | omega
                                                              | ((ring_nf); (omega))))
                                                        | omega
                                                        |
                                                          (simp [] <;>
                                                              first
                                                              | ((clear * -); (omega))
                                                              | omega
                                                              | ((ring_nf); (omega)))) :
    Ends lim P d (.call p args x ;; s) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.callTo hp h ha hd le_rfl) hT

end

end Light

end
end

section


/-!
# Tactics for proofs about programs

A proof about a program follows the text of the program from top to bottom.  The goal is always
`Ends lim P d s ⟨frame l, μ⟩ T Q`, and the statement at the head of `s` decides what comes next:

| the head of the program | what to write                  | what it is told                       |
|-------------------------|--------------------------------|---------------------------------------|
| `x := e`                | `light_set z`                  | the value `z` of `e`                  |
| `mem[a] := e`           | `light_store b z`              | the address `b` and the value `z`     |
| `if c then … else …`    | `light_if h₁ h₂ : p`           | what the test says, and two names     |
| `x := p(args)`          | `light_call fact with …`       | what the procedure does (`Meets`)     |
| a piece with a lemma    | `light_piece fact with …`      | what the piece does (`Ends`)          |
| `skip`, nothing else    | `light_skip`                   |                                       |
| a loop, nothing else    | `refine Ends.forFrame …`       | invariant and number of rounds        |
| a loop, then more       | `refine Ends.next _ (…)`       | the loop's rule with `(hT := le_rfl)` |

Each tactic works whether or not more program follows, hands the steps that are left to the rest of
the program, and proves the side conditions (the expressions stay within the limits and have the
values that were given, the time suffices) by `light_side` and `light_time`.  What is left is the
goal about the rest of the program, or `Q` of the last state.  After `light_if` there are two goals,
first the one in which the test holds.  The patterns after `with` take apart, as those of `rintro`
do, what holds after the call or the piece.  Goals for holes `?_` in a `fact` come before the goal
about the rest of the program.

The side conditions are decided by linear arithmetic over the hypotheses in the context.
`light_facts H` puts the fields of a record `H` there.  What a side condition needs beyond that is
named after `using`: the content of a cell that is read, a definition to be unfolded, a running time
to be unfolded: `light_set K[j] using hkey`.

A program that is a definition is replaced by its text when a single statement is treated.  A
definition that stands at the head of a sequence stays closed: it is a piece, for `light_piece`.
-/

@[expose] public section

namespace Light

/-! ## Records -/



/-! ## One statement -/





























end Light

end
end

section


/-!
# Original-input histograms give the exact independently trimmed sources

The histogram keys retain the first modular reduction and the signed carry
offset. Looking up the endpoint's final residue therefore counts precisely
the original divisibility condition in `BlockEncoding`. An explicit finite
enumeration accounts for every original input incidence once.
-/

namespace ThreeSum.BlockSourceEncoding

open Finset BlockEncoding GlobalEncoding LocalCoverBounds LightSourceResidues
open scoped BigOperators

set_option maxHeartbeats 1000000





































@[simp] theorem modulus_cast (h J : ℕ) : (modulus h J : ℤ) = globalModulus h J := by
  simp only [modulus,globalModulus,Nat.cast_pow]

section OriginalSources

variable {β : Type*} [DecidableEq β]



























end OriginalSources

end ThreeSum.BlockSourceEncoding

end

section


/-!
# Execute the guarded reporter from the two concrete packed records

This procedure loads the twenty-cell owner/source selection and fourteen
computed scratch pointers, reads the retained prime and trim cap, and
passes exactly the verified guarded reporter's forty-four arguments.
Its compositional law retains the supplied reporter postcondition unchanged.
-/

namespace ThreeSum.LightReportingWantedRecordCall

open Light GlobalEncoding LocalCoverBounds LightBlockQuery ReportingHostWantedLayout
open ReportingHostWantedControls

set_option maxHeartbeats 5500000
set_option maxRecDepth 24000
set_option linter.unusedVariables false























































theorem program_meets_sourceProof {lim : Limits} {μ : ℕ→ℤ} {S : Selection} {L : Layout}
    {selectionHeader layoutHeader cover counter h J K d T : ℕ} {Q : ℤ→(ℕ→ℤ)→Prop}
    (H : Seg μ selectionHeader (record S)) (HL : SegN μ layoutHeader (values L))
    (hprime : μ (cover+6)=(localPrime h : ℤ))
    (hcap : μ (cover+7)=(localBucketCap h : ℤ))
    (hw : (lim.space : ℤ)≤lim.word) (hd : d<lim.depth)
    (hs : space selectionHeader layoutHeader cover counter h J K≤lim.space)
    (hselected : ∀ x∈record S, |x|≤lim.word)
    (hlayout : ∀ x∈values L, x≤lim.space)
    (hreport : Meets lim LightReportingWanted.program 137 (d+1)
      (arguments S L layoutHeader cover counter h J K) μ T Q) :
    Meets lim program 138 d
      [selectionHeader,layoutHeader,h,J,K,BlockSourceEncoding.modulus h J,cover,counter]
      μ (T+4000) Q := by
  have hs0 : μ (((selectionHeader : ℤ)+0).toNat)=S.av := by
    rw [show ((selectionHeader : ℤ)+0).toNat=selectionHeader+0 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 0) (by simp [record]) 0
  have hs1 : μ (((selectionHeader : ℤ)+1).toNat)=(S.owner : ℤ) := by
    rw [show ((selectionHeader : ℤ)+1).toNat=selectionHeader+1 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 1) (by simp [record]) 0
  have hs2 : μ (((selectionHeader : ℤ)+2).toNat)=(S.bandB : ℤ) := by
    rw [show ((selectionHeader : ℤ)+2).toNat=selectionHeader+2 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 2) (by simp [record]) 0
  have hs3 : μ (((selectionHeader : ℤ)+3).toNat)=(S.bandC : ℤ) := by
    rw [show ((selectionHeader : ℤ)+3).toNat=selectionHeader+3 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 3) (by simp [record]) 0
  have hs4 : μ (((selectionHeader : ℤ)+4).toNat)=(S.catalog : ℤ) := by
    rw [show ((selectionHeader : ℤ)+4).toNat=selectionHeader+4 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 4) (by simp [record]) 0
  have hs5 : μ (((selectionHeader : ℤ)+5).toNat)=(S.srcL : ℤ) := by
    rw [show ((selectionHeader : ℤ)+5).toNat=selectionHeader+5 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 5) (by simp [record]) 0
  have hs6 : μ (((selectionHeader : ℤ)+6).toNat)=(S.srcR : ℤ) := by
    rw [show ((selectionHeader : ℤ)+6).toNat=selectionHeader+6 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 6) (by simp [record]) 0
  have hs7 : μ (((selectionHeader : ℤ)+7).toNat)=(S.offsetsL : ℤ) := by
    rw [show ((selectionHeader : ℤ)+7).toNat=selectionHeader+7 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 7) (by simp [record]) 0
  have hs8 : μ (((selectionHeader : ℤ)+8).toNat)=(S.flatL : ℤ) := by
    rw [show ((selectionHeader : ℤ)+8).toNat=selectionHeader+8 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 8) (by simp [record]) 0
  have hs9 : μ (((selectionHeader : ℤ)+9).toNat)=(S.offsetsR : ℤ) := by
    rw [show ((selectionHeader : ℤ)+9).toNat=selectionHeader+9 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 9) (by simp [record]) 0
  have hs10 : μ (((selectionHeader : ℤ)+10).toNat)=(S.flatR : ℤ) := by
    rw [show ((selectionHeader : ℤ)+10).toNat=selectionHeader+10 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 10) (by simp [record]) 0
  have hs11 : μ (((selectionHeader : ℤ)+11).toNat)=(S.NL : ℤ) := by
    rw [show ((selectionHeader : ℤ)+11).toNat=selectionHeader+11 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 11) (by simp [record]) 0
  have hs12 : μ (((selectionHeader : ℤ)+12).toNat)=(S.NR : ℤ) := by
    rw [show ((selectionHeader : ℤ)+12).toNat=selectionHeader+12 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 12) (by simp [record]) 0
  have hs13 : μ (((selectionHeader : ℤ)+13).toNat)=(S.baseL : ℤ) := by
    rw [show ((selectionHeader : ℤ)+13).toNat=selectionHeader+13 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 13) (by simp [record]) 0
  have hs14 : μ (((selectionHeader : ℤ)+14).toNat)=(S.baseR : ℤ) := by
    rw [show ((selectionHeader : ℤ)+14).toNat=selectionHeader+14 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 14) (by simp [record]) 0
  have hs15 : μ (((selectionHeader : ℤ)+15).toNat)=(S.occ : ℤ) := by
    rw [show ((selectionHeader : ℤ)+15).toNat=selectionHeader+15 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 15) (by simp [record]) 0
  have hs16 : μ (((selectionHeader : ℤ)+16).toNat)=(S.maps : ℤ) := by
    rw [show ((selectionHeader : ℤ)+16).toNat=selectionHeader+16 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 16) (by simp [record]) 0
  have hs17 : μ (((selectionHeader : ℤ)+17).toNat)=(S.candidates : ℤ) := by
    rw [show ((selectionHeader : ℤ)+17).toNat=selectionHeader+17 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 17) (by simp [record]) 0
  have hs18 : μ (((selectionHeader : ℤ)+18).toNat)=(S.histL : ℤ) := by
    rw [show ((selectionHeader : ℤ)+18).toNat=selectionHeader+18 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 18) (by simp [record]) 0
  have hs19 : μ (((selectionHeader : ℤ)+19).toNat)=(S.histR : ℤ) := by
    rw [show ((selectionHeader : ℤ)+19).toNat=selectionHeader+19 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 19) (by simp [record]) 0
  have hl0 : μ (((layoutHeader : ℤ)+0).toNat)=(L.root : ℤ) := by
    rw [show ((layoutHeader : ℤ)+0).toNat=layoutHeader+0 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 0) (by simp [values]) 0
  have hl1 : μ (((layoutHeader : ℤ)+1).toNat)=(L.masks : ℤ) := by
    rw [show ((layoutHeader : ℤ)+1).toNat=layoutHeader+1 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 1) (by simp [values]) 0
  have hl2 : μ (((layoutHeader : ℤ)+2).toNat)=(L.childL : ℤ) := by
    rw [show ((layoutHeader : ℤ)+2).toNat=layoutHeader+2 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 2) (by simp [values]) 0
  have hl3 : μ (((layoutHeader : ℤ)+3).toNat)=(L.childR : ℤ) := by
    rw [show ((layoutHeader : ℤ)+3).toNat=layoutHeader+3 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 3) (by simp [values]) 0
  have hl4 : μ (((layoutHeader : ℤ)+4).toNat)=(L.counts : ℤ) := by
    rw [show ((layoutHeader : ℤ)+4).toNat=layoutHeader+4 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 4) (by simp [values]) 0
  have hl5 : μ (((layoutHeader : ℤ)+5).toNat)=(L.selected : ℤ) := by
    rw [show ((layoutHeader : ℤ)+5).toNat=layoutHeader+5 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 5) (by simp [values]) 0
  have hl6 : μ (((layoutHeader : ℤ)+6).toNat)=(L.maskBase : ℤ) := by
    rw [show ((layoutHeader : ℤ)+6).toNat=layoutHeader+6 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 6) (by simp [values]) 0
  have hl7 : μ (((layoutHeader : ℤ)+7).toNat)=(L.terminalMasks : ℤ) := by
    rw [show ((layoutHeader : ℤ)+7).toNat=layoutHeader+7 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 7) (by simp [values]) 0
  have hl8 : μ (((layoutHeader : ℤ)+8).toNat)=(L.masksL : ℤ) := by
    rw [show ((layoutHeader : ℤ)+8).toNat=layoutHeader+8 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 8) (by simp [values]) 0
  have hl9 : μ (((layoutHeader : ℤ)+9).toNat)=(L.masksR : ℤ) := by
    rw [show ((layoutHeader : ℤ)+9).toNat=layoutHeader+9 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 9) (by simp [values]) 0
  have hl10 : μ (((layoutHeader : ℤ)+10).toNat)=(L.base : ℤ) := by
    rw [show ((layoutHeader : ℤ)+10).toNat=layoutHeader+10 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 10) (by simp [values]) 0
  have hl11 : μ (((layoutHeader : ℤ)+11).toNat)=(L.bitBase : ℤ) := by
    rw [show ((layoutHeader : ℤ)+11).toNat=layoutHeader+11 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 11) (by simp [values]) 0
  have hl12 : μ (((layoutHeader : ℤ)+12).toNat)=(L.rowOut : ℤ) := by
    rw [show ((layoutHeader : ℤ)+12).toNat=layoutHeader+12 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 12) (by simp [values]) 0
  have hl13 : μ (((layoutHeader : ℤ)+13).toNat)=(L.work : ℤ) := by
    rw [show ((layoutHeader : ℤ)+13).toNat=layoutHeader+13 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 13) (by simp [values]) 0
  have hv0 : |S.av|≤lim.word := hselected _ (by simp [record])
  have hv1 : (S.owner : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.owner : ℤ) (by simp [record])
  have hv2 : (S.bandB : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.bandB : ℤ) (by simp [record])
  have hv3 : (S.bandC : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.bandC : ℤ) (by simp [record])
  have hv4 : (S.catalog : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.catalog : ℤ) (by simp [record])
  have hv5 : (S.srcL : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.srcL : ℤ) (by simp [record])
  have hv6 : (S.srcR : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.srcR : ℤ) (by simp [record])
  have hv7 : (S.offsetsL : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.offsetsL : ℤ) (by simp [record])
  have hv8 : (S.flatL : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.flatL : ℤ) (by simp [record])
  have hv9 : (S.offsetsR : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.offsetsR : ℤ) (by simp [record])
  have hv10 : (S.flatR : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.flatR : ℤ) (by simp [record])
  have hv11 : (S.NL : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.NL : ℤ) (by simp [record])
  have hv12 : (S.NR : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.NR : ℤ) (by simp [record])
  have hv13 : (S.baseL : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.baseL : ℤ) (by simp [record])
  have hv14 : (S.baseR : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.baseR : ℤ) (by simp [record])
  have hv15 : (S.occ : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.occ : ℤ) (by simp [record])
  have hv16 : (S.maps : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.maps : ℤ) (by simp [record])
  have hv17 : (S.candidates : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.candidates : ℤ) (by simp [record])
  have hv18 : (S.histL : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.histL : ℤ) (by simp [record])
  have hv19 : (S.histR : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.histR : ℤ) (by simp [record])
  have hw0 : L.root≤lim.space := hlayout _ (by simp [values])
  have hw1 : L.masks≤lim.space := hlayout _ (by simp [values])
  have hw2 : L.childL≤lim.space := hlayout _ (by simp [values])
  have hw3 : L.childR≤lim.space := hlayout _ (by simp [values])
  have hw4 : L.counts≤lim.space := hlayout _ (by simp [values])
  have hw5 : L.selected≤lim.space := hlayout _ (by simp [values])
  have hw6 : L.maskBase≤lim.space := hlayout _ (by simp [values])
  have hw7 : L.terminalMasks≤lim.space := hlayout _ (by simp [values])
  have hw8 : L.masksL≤lim.space := hlayout _ (by simp [values])
  have hw9 : L.masksR≤lim.space := hlayout _ (by simp [values])
  have hw10 : L.base≤lim.space := hlayout _ (by simp [values])
  have hw11 : L.bitBase≤lim.space := hlayout _ (by simp [values])
  have hw12 : L.rowOut≤lim.space := hlayout _ (by simp [values])
  have hw13 : L.work≤lim.space := hlayout _ (by simp [values])
  have hs' := hs
  unfold space numericExtra at hs'
  have hprimeZ : μ (((cover : ℤ)+6).toNat)=(localPrime h : ℤ) := by
    rw [show ((cover : ℤ)+6).toNat=cover+6 by omega]; exact hprime
  have hcapZ : μ (((cover : ℤ)+7).toNat)=(localBucketCap h : ℤ) := by
    rw [show ((cover : ℤ)+7).toNat=cover+7 by omega]; exact hcap
  have hcutZ : (J : ℤ)*(2*(h : ℤ))=(sourceCut h J : ℤ) := by simp [sourceCut]; ring
  have hcutNonneg : (0 : ℤ)≤(J : ℤ)*(2*(h : ℤ)) := by positivity
  have hcutWord : (J : ℤ)*(2*(h : ℤ))≤lim.word := by
    rw [hcutZ]
    exact (Int.ofNat_le.mpr (by omega : sourceCut h J≤lim.space)).trans hw
  have hcutNonneg' : (0 : ℤ)≤2*(h : ℤ)*(J : ℤ) := by positivity
  have hcutWord' : 2*(h : ℤ)*(J : ℤ)≤lim.word := by
    nlinarith only [hcutWord]
  have hrawZ : (layoutHeader : ℤ)+18+(J : ℤ)=(rawRows layoutHeader J : ℤ) := by
    simp [rawRows,decoded]; ring
  have hpackedZ : (layoutHeader : ℤ)+38+2*(J : ℤ)=(packed layoutHeader J : ℤ) := by
    simp [packed,access,decoded]; ring
  have hs0Nat : μ selectionHeader=S.av := by simpa only [add_zero,Int.toNat_natCast] using hs0
  have hl0Nat : μ layoutHeader=(L.root : ℤ) := by simpa only [add_zero,Int.toNat_natCast] using hl0
  have hs1Nat : μ (selectionHeader+1)=(S.owner : ℤ) := by
    rw [show selectionHeader+1=((selectionHeader : ℤ)+1).toNat by omega]; exact hs1
  have hs2Nat : μ (selectionHeader+2)=(S.bandB : ℤ) := by
    rw [show selectionHeader+2=((selectionHeader : ℤ)+2).toNat by omega]; exact hs2
  have hs3Nat : μ (selectionHeader+3)=(S.bandC : ℤ) := by
    rw [show selectionHeader+3=((selectionHeader : ℤ)+3).toNat by omega]; exact hs3
  have hs4Nat : μ (selectionHeader+4)=(S.catalog : ℤ) := by
    rw [show selectionHeader+4=((selectionHeader : ℤ)+4).toNat by omega]; exact hs4
  have hs5Nat : μ (selectionHeader+5)=(S.srcL : ℤ) := by
    rw [show selectionHeader+5=((selectionHeader : ℤ)+5).toNat by omega]; exact hs5
  have hs6Nat : μ (selectionHeader+6)=(S.srcR : ℤ) := by
    rw [show selectionHeader+6=((selectionHeader : ℤ)+6).toNat by omega]; exact hs6
  have hs7Nat : μ (selectionHeader+7)=(S.offsetsL : ℤ) := by
    rw [show selectionHeader+7=((selectionHeader : ℤ)+7).toNat by omega]; exact hs7
  have hs8Nat : μ (selectionHeader+8)=(S.flatL : ℤ) := by
    rw [show selectionHeader+8=((selectionHeader : ℤ)+8).toNat by omega]; exact hs8
  have hs9Nat : μ (selectionHeader+9)=(S.offsetsR : ℤ) := by
    rw [show selectionHeader+9=((selectionHeader : ℤ)+9).toNat by omega]; exact hs9
  have hs10Nat : μ (selectionHeader+10)=(S.flatR : ℤ) := by
    rw [show selectionHeader+10=((selectionHeader : ℤ)+10).toNat by omega]; exact hs10
  have hs11Nat : μ (selectionHeader+11)=(S.NL : ℤ) := by
    rw [show selectionHeader+11=((selectionHeader : ℤ)+11).toNat by omega]; exact hs11
  have hs12Nat : μ (selectionHeader+12)=(S.NR : ℤ) := by
    rw [show selectionHeader+12=((selectionHeader : ℤ)+12).toNat by omega]; exact hs12
  have hs13Nat : μ (selectionHeader+13)=(S.baseL : ℤ) := by
    rw [show selectionHeader+13=((selectionHeader : ℤ)+13).toNat by omega]; exact hs13
  have hs14Nat : μ (selectionHeader+14)=(S.baseR : ℤ) := by
    rw [show selectionHeader+14=((selectionHeader : ℤ)+14).toNat by omega]; exact hs14
  have hs15Nat : μ (selectionHeader+15)=(S.occ : ℤ) := by
    rw [show selectionHeader+15=((selectionHeader : ℤ)+15).toNat by omega]; exact hs15
  have hs16Nat : μ (selectionHeader+16)=(S.maps : ℤ) := by
    rw [show selectionHeader+16=((selectionHeader : ℤ)+16).toNat by omega]; exact hs16
  have hs17Nat : μ (selectionHeader+17)=(S.candidates : ℤ) := by
    rw [show selectionHeader+17=((selectionHeader : ℤ)+17).toNat by omega]; exact hs17
  have hs18Nat : μ (selectionHeader+18)=(S.histL : ℤ) := by
    rw [show selectionHeader+18=((selectionHeader : ℤ)+18).toNat by omega]; exact hs18
  have hs19Nat : μ (selectionHeader+19)=(S.histR : ℤ) := by
    rw [show selectionHeader+19=((selectionHeader : ℤ)+19).toNat by omega]; exact hs19
  have hl1Nat : μ (layoutHeader+1)=(L.masks : ℤ) := by
    rw [show layoutHeader+1=((layoutHeader : ℤ)+1).toNat by omega]; exact hl1
  have hl2Nat : μ (layoutHeader+2)=(L.childL : ℤ) := by
    rw [show layoutHeader+2=((layoutHeader : ℤ)+2).toNat by omega]; exact hl2
  have hl3Nat : μ (layoutHeader+3)=(L.childR : ℤ) := by
    rw [show layoutHeader+3=((layoutHeader : ℤ)+3).toNat by omega]; exact hl3
  have hl4Nat : μ (layoutHeader+4)=(L.counts : ℤ) := by
    rw [show layoutHeader+4=((layoutHeader : ℤ)+4).toNat by omega]; exact hl4
  have hl5Nat : μ (layoutHeader+5)=(L.selected : ℤ) := by
    rw [show layoutHeader+5=((layoutHeader : ℤ)+5).toNat by omega]; exact hl5
  have hl6Nat : μ (layoutHeader+6)=(L.maskBase : ℤ) := by
    rw [show layoutHeader+6=((layoutHeader : ℤ)+6).toNat by omega]; exact hl6
  have hl7Nat : μ (layoutHeader+7)=(L.terminalMasks : ℤ) := by
    rw [show layoutHeader+7=((layoutHeader : ℤ)+7).toNat by omega]; exact hl7
  have hl8Nat : μ (layoutHeader+8)=(L.masksL : ℤ) := by
    rw [show layoutHeader+8=((layoutHeader : ℤ)+8).toNat by omega]; exact hl8
  have hl9Nat : μ (layoutHeader+9)=(L.masksR : ℤ) := by
    rw [show layoutHeader+9=((layoutHeader : ℤ)+9).toNat by omega]; exact hl9
  have hl10Nat : μ (layoutHeader+10)=(L.base : ℤ) := by
    rw [show layoutHeader+10=((layoutHeader : ℤ)+10).toNat by omega]; exact hl10
  have hl11Nat : μ (layoutHeader+11)=(L.bitBase : ℤ) := by
    rw [show layoutHeader+11=((layoutHeader : ℤ)+11).toNat by omega]; exact hl11
  have hl12Nat : μ (layoutHeader+12)=(L.rowOut : ℤ) := by
    rw [show layoutHeader+12=((layoutHeader : ℤ)+12).toNat by omega]; exact hl12
  have hl13Nat : μ (layoutHeader+13)=(L.work : ℤ) := by
    rw [show layoutHeader+13=((layoutHeader : ℤ)+13).toNat by omega]; exact hl13
  apply Meets.of_body (p := 138) (by rfl : program[138]?=some (body 137))
  unfold body
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (S.av : ℤ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hs0Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hs0Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hs0Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (S.owner : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hs1,
                hs1Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hs1, hs1Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hs1, hs1Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (S.bandB : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hs2,
                hs2Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hs2, hs2Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hs2, hs2Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (S.bandC : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hs3,
                hs3Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hs3, hs3Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hs3, hs3Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (S.catalog : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hs4,
                hs4Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hs4, hs4Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hs4, hs4Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (S.srcL : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hs5,
                hs5Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hs5, hs5Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hs5, hs5Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (S.srcR : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hs6,
                hs6Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hs6, hs6Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hs6, hs6Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (S.offsetsL : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hs7,
                hs7Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hs7, hs7Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hs7, hs7Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (S.flatL : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hs8,
                hs8Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hs8, hs8Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hs8, hs8Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (S.offsetsR : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hs9,
                hs9Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hs9, hs9Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hs9, hs9Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (S.flatR : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hs10,
                hs10Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hs10, hs10Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hs10, hs10Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (S.NL : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hs11,
                hs11Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hs11, hs11Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hs11, hs11Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (S.NR : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hs12,
                hs12Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hs12, hs12Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hs12, hs12Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (S.baseL : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hs13,
                hs13Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hs13, hs13Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hs13, hs13Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (S.baseR : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hs14,
                hs14Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hs14, hs14Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hs14, hs14Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (S.occ : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hs15,
                hs15Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hs15, hs15Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hs15, hs15Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (S.maps : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hs16,
                hs16Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hs16, hs16Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hs16, hs16Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (S.candidates : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hs17,
                hs17Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hs17, hs17Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hs17, hs17Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (S.histL : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hs18,
                hs18Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hs18, hs18Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hs18, hs18Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (S.histR : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hs19,
                hs19Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hs19, hs19Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hs19, hs19Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (L.root : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hl0Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hl0Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hl0Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (L.masks : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hl1,
                hl1Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hl1, hl1Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hl1, hl1Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (L.childL : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hl2,
                hl2Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hl2, hl2Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hl2, hl2Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (L.childR : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hl3,
                hl3Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hl3, hl3Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hl3, hl3Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (L.counts : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hl4,
                hl4Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hl4, hl4Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hl4, hl4Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (L.selected : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hl5,
                hl5Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hl5, hl5Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hl5, hl5Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (L.maskBase : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hl6,
                hl6Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hl6, hl6Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hl6, hl6Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (L.terminalMasks : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hl7,
                hl7Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hl7, hl7Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hl7, hl7Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (L.masksL : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hl8,
                hl8Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hl8, hl8Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hl8, hl8Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (L.masksR : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hl9,
                hl9Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hl9, hl9Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hl9, hl9Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (L.base : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hl10,
                hl10Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hl10, hl10Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hl10, hl10Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (L.bitBase : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hl11,
                hl11Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hl11, hl11Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hl11, hl11Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (L.rowOut : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hl12,
                hl12Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hl12, hl12Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hl12, hl12Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (L.work : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hl13,
                hl13Nat]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hl13, hl13Nat] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hl13, hl13Nat] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (localPrime h : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hprimeZ]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hprimeZ] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hprimeZ] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (localBucketCap h : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hcapZ]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hcapZ] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hcapZ] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (512 * h : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (sourceCut h J : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hcutZ]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hcutZ] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hcutZ] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (rawRows layoutHeader J : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hrawZ,
                rawRows, decoded]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hrawZ, rawRows, decoded] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hrawZ, rawRows, decoded] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
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
    (refine Light.Ends.setToThen (packed layoutHeader J : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hpackedZ, packed, access, decoded]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hpackedZ, packed, access, decoded] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hpackedZ, packed, access,
                decoded] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  have hreportRun := hreport.append [body 137]
  change Meets lim program 137 (d+1) _ μ T Q at hreportRun
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
      | refine Light.Ends.callToThen (hreportRun _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hreportRun ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                arguments]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [arguments] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, arguments] <;>
              first
              | assumption
              |
                ((clear * - hw hs' hcutWord hcutWord' hcutNonneg hcutNonneg' hv0
                      hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14
                      hv15 hv16 hv17 hv18 hv19 hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8
                      hw9 hw10 hw11 hw12 hw13);
                  (omega))
              | omega)));
    (on_goal -1 =>
        ((rintro result ν hpost);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  exact hpost

end ThreeSum.LightReportingWantedRecordCall


end


theorem solution : ∀ {lim : Light.Limits} {μ : Nat → Int} {S : ThreeSum.ReportingHostWantedControls.Selection}
  {L : ThreeSum.ReportingHostWantedLayout.Layout} {selectionHeader layoutHeader cover counter h J K d T : Nat}
  {Q : Int → (Nat → Int) → Prop} (H : Light.Seg μ selectionHeader (ThreeSum.ReportingHostWantedControls.record S))
  (HL : Light.SegN μ layoutHeader (ThreeSum.ReportingHostWantedLayout.values L))
  (hprime :
    @Eq.{1} Int
      (μ
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cover
          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
      (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LocalCoverBounds.localPrime h)))
  (hcap :
    @Eq.{1} Int
      (μ
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cover
          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
      (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LocalCoverBounds.localBucketCap h)))
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd : @LT.lt.{0} Nat instLTNat d lim.depth)
  (hs :
    @LE.le.{0} Nat instLENat
      (ThreeSum.LightReportingWantedRecordCall.space selectionHeader layoutHeader cover counter h J K) lim.space)
  (hselected :
    ∀ (x : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int)
          (ThreeSum.ReportingHostWantedControls.record S) x →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup x) lim.word)
  (hlayout :
    ∀ (x : Nat),
      @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
          (ThreeSum.ReportingHostWantedLayout.values L) x →
        @LE.le.{0} Nat instLENat x lim.space)
  (hreport :
    Light.Meets lim ThreeSum.LightReportingWanted.program
      (@OfNat.ofNat.{0} Nat (nat_lit 137) (instOfNatNat (nat_lit 137)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (ThreeSum.ReportingHostWantedControls.arguments S L layoutHeader cover counter h J K) μ T Q),
  Light.Meets lim ThreeSum.LightReportingWantedRecordCall.program
    (@OfNat.ofNat.{0} Nat (nat_lit 138) (instOfNatNat (nat_lit 138))) d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt selectionHeader)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt layoutHeader)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt K)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.BlockSourceEncoding.modulus h J))
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cover)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt counter) (@List.nil.{0} Int)))))))))
    μ
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) T
      (@OfNat.ofNat.{0} Nat (nat_lit 4000) (instOfNatNat (nat_lit 4000))))
    Q := by
  exact @ThreeSum.LightReportingWantedRecordCall.program_meets_sourceProof

#print axioms solution
