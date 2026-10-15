-- Prove2me | solution 1 for ThreeSum.LightReportingTerminalFrontier.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:59:58.370429+00:00
-- url     : https://prove2.me/submissions/019defc4-9e4c-44b3-b52d-2907e3538cbb

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
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
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
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
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
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
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
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_BlockSourceCoverInput_Input_of_kept
import Theorems.Thm_ThreeSum_LightReportingTerminal_program_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightBlockSourceBuild
end ThreeSum.LightBlockSourceBuild
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightReportingTerminalMasks
end ThreeSum.LightReportingTerminalMasks
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostBucketTest
end ThreeSum.ReportingHostBucketTest
namespace ThreeSum.ReportingHostTerminalFrontier
end ThreeSum.ReportingHostTerminalFrontier
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting

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




















































/-- A branch, followed by the rest of the program: each side, with the rest of the program behind
it, gets the steps that the test leaves. -/
theorem Ends.iteThen {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ s : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d ((Light.Stmt.seq s₁ s)) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → Ends lim P d ((Light.Stmt.seq s₂ s)) σ (T - (c.cost + 1)) Q)
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
    Ends lim P d ((Light.Stmt.seq (.ite c s₁ s₂) s)) σ T Q := by
  by_cases hc : c.Holds σ
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₁ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteTrue hs hc he₁) he₂, by omega, hq⟩
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₂ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, .seq (.iteFalse hs hc he₁) he₂, by omega, hq⟩

/-- A branch, followed by the rest of the program, where the test says `p`: the first side is run
under the hypothesis `p`, the second under `¬ p`. -/
theorem Ends.iteIffThen {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ s : Stmt} {Q : State → Prop}
    (p : Prop) (h₁ : p → Ends lim P d ((Light.Stmt.seq s₁ s)) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ p → Ends lim P d ((Light.Stmt.seq s₂ s)) σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ ∧ (c.Holds σ ↔ p) := by (((try have := Light.Std.space_le (by assumption)));
                                                       ((try have := Light.Std.const_le (by assumption)));
                                                       (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)))
    (hT : c.cost + 1 ≤ T := by first
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
                                       | ((ring_nf); (omega)))) : Ends lim P d ((Light.Stmt.seq (.ite c s₁ s₂) s)) σ T Q :=
  Ends.iteThen (fun hc => h₁ (hs.2.1 hc)) (fun hc => h₂ fun hp => hc (hs.2.2 hp)) hs.1 hT

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
# Original-input residue keys with a carry offset

The source histogram uses `(x % p + shift) % m`, with two independently
chosen moduli. This procedure computes both remainders from each original
signed input and retains every incidence, including duplicate values.
-/

namespace ThreeSum.LightSourceResidues

open Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000



theorem key_cast {p m : ℕ} (hm : 0 < m) (shift x : ℤ) :
    (key p m shift x : ℤ) = (x % (p : ℤ) + shift) % (m : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne'))

theorem key_lt {p m : ℕ} (hm : 0 < m) (shift x : ℤ) : key p m shift x < m := by
  have h := Int.emod_lt_of_pos (x % (p : ℤ) + shift)
    (by exact_mod_cast hm : (0 : ℤ) < m)
  rw [← key_cast hm] at h
  exact_mod_cast h
























variable {lim : Limits} {P : Program} {d : ℕ}

















































































































end ThreeSum.LightSourceResidues

end

section


/-!
# A linear-time histogram procedure in the benchmark language

The input is an array of already computed residue indices in `[0,p)`.
The output is cleared and incremented once per input item. Multiplicities
are retained, including repeated equal residues.
-/

namespace ThreeSum.LightHistogram

open Light Finset

variable {lim : Limits} {P : Program} {d : ℕ}










theorem count_succ (key : ℕ → ℕ) (r i : ℕ) :
    count key r (i + 1) = count key r i + if key i = r then 1 else 0 := by
  unfold count
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases heq : key i = r
  · rw [if_pos heq, Finset.card_insert_of_notMem (by simp)]
    simp [heq]
  · simp [heq]





























































































end ThreeSum.LightHistogram

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



































theorem modulus_pos (h J : ℕ) : 0 < modulus h J := pow_pos (localPrime_pos h) J

@[simp] theorem modulus_cast (h J : ℕ) : (modulus h J : ℤ) = globalModulus h J := by
  simp only [modulus,globalModulus,Nat.cast_pow]

section OriginalSources

variable {β : Type*} [DecidableEq β]



























end OriginalSources

end ThreeSum.BlockSourceEncoding

end

section


/-!
# Exact positions of original indices in retained residue buckets

Counting-sort positions preserve every input incidence. The resulting fiber
segments contain no repeated physical indices even when input values agree.
All inverse-enumeration reasoning is semantic; the actual scatter program
writes these positions using a cursor and never searches an input band.
-/

namespace ThreeSum.SourceBuckets

open Finset LightHistogram

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000






theorem offset_succ (key : ℕ → ℕ) (N r : ℕ) :
    offset key N (r+1) = offset key N r+count key r N := by
  exact Finset.sum_range_succ _ _

theorem offset_mono (key : ℕ → ℕ) (N : ℕ) : Monotone (offset key N) := by
  intro r s hrs
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hrs)

theorem count_mono (key : ℕ → ℕ) (r : ℕ) : Monotone (count key r) := by
  intro i j hij
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hij))

theorem count_strict {key : ℕ → ℕ} {r i j : ℕ} (hij : i < j) (hkey : key i = r) :
    count key r i < count key r j := by
  have he := count_succ key r i
  simp only [hkey,ite_true] at he
  have hm := count_mono key r (show i+1 ≤ j by omega)
  omega

theorem offset_total {key : ℕ → ℕ} {N M : ℕ} (hkey : ∀ i < N, key i < M) :
    offset key N M = N := by
  unfold offset count
  have he := Finset.card_eq_sum_card_fiberwise
    (f := key) (s := range N) (t := range M)
    (fun i hi => Finset.mem_range.mpr (hkey i (Finset.mem_range.mp hi)))
  simpa only [Finset.card_range] using he.symm

theorem offset_le {key : ℕ → ℕ} {N M r : ℕ} (hkey : ∀ i < N, key i < M) (hr : r ≤ M) :
    offset key N r ≤ N := by
  exact (offset_mono key N hr).trans_eq (offset_total hkey)






theorem position_end {key : ℕ → ℕ} {N i : ℕ} (hi : i < N) :
    position key N i < offset key N (key i+1) := by
  rw [offset_succ]
  exact Nat.add_lt_add_left (count_strict hi rfl) _

theorem position_lt {key : ℕ → ℕ} {N M i : ℕ} (hkey : ∀ i < N, key i < M) (hi : i < N) :
    position key N i < N :=
  (position_end hi).trans_le (offset_le hkey (by have hk := hkey i hi; omega))























































































































end ThreeSum.SourceBuckets

end

section


/-!
# Executable residue selection and original-value leaf decision

The host reduces the two actual endpoint values, selects the independently
trimmed physical buckets, and tests original values. Its Boolean result has
a memory-independent physical-index specification, suitable for sequential
candidate batching with the exact sum of the selected pair costs.
-/

namespace ThreeSum.LightReportingLeaf

open Light SourceBuckets LightResidues ReportingHostBucketTest

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000


















theorem stored_of_kept {μ ν : ℕ→ℤ} {key : ℕ→ℕ} {N Mo offsets flat stop : ℕ}
    (H : Stored μ key N Mo offsets flat) (hkey : ∀ i<N, key i<Mo)
    (hoffsets : offsets+Mo+1≤stop) (hflat : flat+N≤stop) (hkeep : Kept μ ν stop) :
    Stored ν key N Mo offsets flat := by
  constructor
  · intro r hr
    exact (hkeep _ (by omega)).trans (H.offsets r hr)
  · intro i hi
    have hpos := position_lt hkey hi
    exact (hkeep _ (by omega)).trans (H.indices i hi)

variable {lim : Limits}


















































































end ThreeSum.LightReportingLeaf

end

section


/-!
# Exact terminal-prefix order, summed cost, and original completeness

The prefix batch consumes the actual retained frontier order. Every local
scan keeps its own selected-pair charge; their sum is bounded by the exact
original raw mass at the partial depth.
-/

namespace ThreeSum.ReportingHostTerminalFrontier

open Finset BlockRows BlockEncoding GlobalEncoding RawIncidences RawReporting RawPrefixCounts
open StoredReporting LightBlockSourceBuild
open scoped BigOperators

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000











theorem hit_succ {h J : ℕ} (av : ℤ) (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : GlobalOutput h J) (k : ℕ) (pres : List (List (Finset (Fin (512*h))))) (n : ℕ) :
    Hit av p shift left right NL NR q k pres (n+1) ↔
      Hit av p shift left right NL NR q k pres n ∨
      ReportingHostTerminalBatch.Hit av p shift left right NL NR q k (prefixAt pres n) := by
  constructor
  · rintro ⟨i,hi,hh⟩
    by_cases hin : i<n
    · exact Or.inl ⟨i,hin,hh⟩
    · have he : i=n := by omega
      exact Or.inr (he ▸ hh)
  · rintro (⟨i,hi,hh⟩ | hh)
    · exact ⟨i,by omega,hh⟩
    · exact ⟨n,by omega,hh⟩









































variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]





































end ThreeSum.ReportingHostTerminalFrontier

end

section


/-!
# Executed terminal iteration over the retained prefix arrays

The recursion reads the two aligned prefix masks from retained memory and
runs the complete terminal program for each prefix. Its cost is the sum of
the actual prefix costs. Reused scratch never changes the prefix arrays or
the original source buckets, occurrence rows, and selected cover data.
-/

namespace ThreeSum.LightReportingTerminalFrontier

open Light Finset BlockRows BlockIndex BlockEncoding BlockCoefficientRows
open GlobalEncoding LocalCoverBounds BlockSourceEncoding LightSourceResidues SourceBuckets
open BlockIndexedQuery BlockForced StoredReporting LightBlockQuery
open LightReportingTerminalMasks LightBlockSourceBuild ReportingHostTerminalFrontier

set_option maxHeartbeats 3800000
set_option maxRecDepth 14000

















variable {lim : Limits}

theorem program_meets_sourceProof {μ : ℕ→ℤ}
    {h J k srcL srcR offsetsL offsetsR flatL flatR NL NR occ maps candidates histL histR inL inR
      masks masksL masksR base bitBase rowOut work n d : ℕ}
    (av : ℤ) (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ)
    (q : GlobalOutput h J) (pres : List (List (Finset (Fin (512*h))))) (hk : k≤J) (hn : n≤pres.length)
    (HL : Stored μ (fun i => key p (modulus h J) 0 (left i)) NL (modulus h J) offsetsL flatL)
    (HR : Stored μ (fun i => key p (modulus h J) shift (right i)) NR (modulus h J) offsetsR flatR)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+n+count h J k+J*(512*h)+10≤lim.depth)
    (hsrcL : srcL+NL≤masks) (hsrcR : srcR+NR≤masks)
    (hoffsetsL : offsetsL+modulus h J+1≤masks) (hoffsetsR : offsetsR+modulus h J+1≤masks)
    (hflatL : flatL+NL≤masks) (hflatR : flatR+NR≤masks)
    (hocc : occ+J≤masks) (hmaps : maps+2*(512*h)*scheduleSize h≤masks)
    (hcandidates : candidates+scheduleSize h≤masks)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h≤masks)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h≤masks)
    (hinL : inL+pres.length≤masks) (hinR : inR+pres.length≤masks)
    (hmasks : masks+count h J k≤masksL) (hmasksL : masksL+count h J k≤masksR)
    (hmasksR : masksR+count h J k≤base)
    (hstop : LightReportingTerminalPreparation.stop base (J*(512*h)) (count h J k)≤bitBase)
    (hbits : bitBase+J*(512*h)≤rowOut) (hrowOut : rowOut+2≤work)
    (hspace : LightReportingTerminal.space work h J≤lim.space)
    (hword : (LightReportingTerminal.word h J : ℤ)≤lim.word)
    (hoccRead : ∀ j<J, μ (occ+j)=(occurrenceIndices (outputOccurrences q) j : ℤ))
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR)
    (hreadL : ∀ i<NL, μ (srcL+i)=left i) (hreadR : ∀ j<NR, μ (srcR+j)=right j)
    (hreadInL : ∀ i<pres.length, μ (inL+i)=
      (SubsetAddress.subsetMask (leftPrefix k (prefixRows (J := J) (prefixAt pres i))) : ℤ))
    (hreadInR : ∀ i<pres.length, μ (inR+i)=
      (SubsetAddress.subsetMask (rightPrefix k (outputRows q) (prefixRows (J := J) (prefixAt pres i))) : ℤ))
    (hvaluesL : ∀ i<NL, |left i|≤lim.word) (hvaluesR : ∀ j<NR, |right j|≤lim.word)
    (ha : |av|≤lim.word) (htarget : ∀ i<NL, |av+left i|≤lim.word)
    (hcountWord : ((NL*NR : ℕ) : ℤ)≤lim.word) :
    Meets lim program 39 d
      [av,srcL,srcR,offsetsL,flatL,offsetsR,flatR,NL,NR,modulus h J,J,512*h,h,localPrime h,localBucketCap h,
        occ,maps,candidates,histL,histR,k,SubsetAddress.subsetMask (querySet k (outputRows q)),
        inL,inR,masks,masksL,masksR,base,bitBase,rowOut,work,n]
      μ (time p shift left right NL NR q k pres n)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ Hit av p shift left right NL NR q k pres n) ∧ Kept μ ν masks) := by
  have hsOther := (le_max_right _ _).trans hspace
  have hsWork : work≤lim.space := by have hh := (le_max_right _ _).trans hsOther; omega
  have hstop' : base+2*(2*(J*(512*h))+4*count h J k+2)≤bitBase := hstop
  have hmaskSpace : masks≤lim.space := by omega
  have htwo : (2 : ℤ)≤lim.word := by omega
  have hpWord : ((2^(J*(512*h)+1) : ℕ) : ℤ)≤lim.word := by
    exact (Int.ofNat_le.mpr (Nat.le_add_left _ _)).trans hword
  have hmaskWord (S : Finset (Fin (J*(512*h)))) : |(SubsetAddress.subsetMask S : ℤ)|≤lim.word := by
    rw [Int.abs_natCast]
    exact (Int.ofNat_le.mpr ((SubsetAddress.subsetMask_isMask S).1.le.trans
      (Nat.pow_le_pow_right (by decide) (by omega)))).trans hpWord
  have hkeyL : ∀ i<NL, key p (modulus h J) 0 (left i)<modulus h J :=
    fun i _ => key_lt (modulus_pos h J) 0 (left i)
  have hkeyR : ∀ i<NR, key p (modulus h J) shift (right i)<modulus h J :=
    fun i _ => key_lt (modulus_pos h J) shift (right i)
  induction n generalizing μ d with
  | zero =>
      apply Meets.of_body (p := 39) (by rfl : program[39]?=some (body 39 38))
      unfold body ReportingHostTerminalFrontier.time
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
            Light.Ends.iteIffThen ((0 : ℤ) < 0) (fun hbad => ?_) (fun hno => ?_) ?_
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
        (all_goals
            repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)
      · omega
      · focus
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
        exact ⟨by simp,by simp [Hit],SameOn.refl⟩
  | succ n ih =>
      apply Meets.of_body (p := 39) (by rfl : program[39]?=some (body 39 38))
      unfold body
      rw [ReportingHostTerminalFrontier.time]
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
            Light.Ends.iteIffThen ((0 : ℤ) < ((n + 1 : ℕ) : ℤ)) (fun hyes => ?_)
              (fun hbad => ?_) ?_ ?_);
        (on_goal -1 =>
            first
            |
              ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                    LightReportingTerminal.time]);
                (first
                  | omega
                  | ((ring_nf); (omega))))
            | omega
            |
              (simp [LightReportingTerminal.time] <;>
                  first
                  | omega
                  | ((ring_nf); (omega))));
        (on_goal -1 =>
            (((try have := Light.Std.space_le (by assumption)));
              ((try have := Light.Std.const_le (by assumption)));
              (simp [Light.Limits.Addr, abs_le, -abs_mul,
                    LightReportingTerminal.time] <;>
                  omega)));
        (all_goals
            repeat
              with_unfolding_none
                first
                | refine Light.Ends.seqAssoc ?_
                | refine Light.Ends.skipThen ?_)
      · have hrun := ih (μ := μ) (d := d+1) (by omega) HL HR (by omega)
          hoccRead hcover hreadL hreadR hreadInL hreadInR
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
            | refine Light.Ends.callToThen (hrun _ (by omega)) ?_ ?_ ?_ ?_
            | refine Light.Ends.callToThen hrun ?_ ?_ ?_ ?_);
          (on_goal -1 =>
              first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                      LightReportingTerminal.time]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [LightReportingTerminal.time] <;>
                    first
                    | omega
                    | ((ring_nf); (omega))));
          (on_goal -1 => omega);
          (on_goal -1 =>
              (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul,
                      LightReportingTerminal.time] <;>
                    omega)));
          (on_goal -1 =>
              ((rintro prev ν ⟨hprevBool, hprev, hkeep⟩);
                (try with_unfolding_none refine Light.Ends.skip ?_)))
        have HLν := LightReportingLeaf.stored_of_kept HL hkeyL hoffsetsL hflatL hkeep
        have HRν := LightReportingLeaf.stored_of_kept HR hkeyR hoffsetsR hflatR hkeep
        have hcoverν := hcover.of_kept hkeep hmaps hcandidates hleft hright
        have hLmask : ν (inL+n)=
            (SubsetAddress.subsetMask (leftPrefix k (prefixRows (J := J) (prefixAt pres n))) : ℤ) :=
          (hkeep _ (by omega)).trans (hreadInL n (by omega))
        have hRmask : ν (inR+n)=
            (SubsetAddress.subsetMask (rightPrefix k (outputRows q) (prefixRows (J := J) (prefixAt pres n))) : ℤ) :=
          (hkeep _ (by omega)).trans (hreadInR n (by omega))
        have hLword := abs_le.mp (hmaskWord (leftPrefix k (prefixRows (J := J) (prefixAt pres n))))
        have hRword := abs_le.mp (hmaskWord (rightPrefix k (outputRows q) (prefixRows (J := J) (prefixAt pres n))))
        focus
          ((((first
                  | refine Light.Ends.seqSelf ?_
                  | refine Light.Ends.skipLast ?_));
              (repeat
                  with_unfolding_none
                    first
                    | refine Light.Ends.seqAssoc ?_
                    | refine Light.Ends.skipThen ?_)));
          (refine Light.Ends.setToThen (n : ℕ) ?_ ?_ ?_);
          (on_goal -1 =>
              first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                      LightReportingTerminal.time]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [LightReportingTerminal.time] <;>
                    first
                    | omega
                    | ((ring_nf); (omega))));
          (on_goal -1 =>
              (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul,
                      LightReportingTerminal.time] <;>
                    omega)));
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
                (SubsetAddress.subsetMask
                    (leftPrefix k (prefixRows (J := J) (prefixAt pres n))) :
                  ℕ)
                ?_ ?_ ?_);
          (on_goal -1 =>
              first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hLmask,
                      LightReportingTerminal.time]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [hLmask, LightReportingTerminal.time] <;>
                    first
                    | omega
                    | ((ring_nf); (omega))));
          (on_goal -1 =>
              (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul, hLmask,
                      LightReportingTerminal.time] <;>
                    omega)));
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
                (SubsetAddress.subsetMask
                    (rightPrefix k (outputRows q)
                      (prefixRows (J := J) (prefixAt pres n))) :
                  ℕ)
                ?_ ?_ ?_);
          (on_goal -1 =>
              first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hRmask,
                      LightReportingTerminal.time]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [hRmask, LightReportingTerminal.time] <;>
                    first
                    | omega
                    | ((ring_nf); (omega))));
          (on_goal -1 =>
              (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul, hRmask,
                      LightReportingTerminal.time] <;>
                    omega)));
          (try with_unfolding_none refine Light.Ends.skip ?_)
        have hterminal := (LightReportingTerminal.program_meets (μ := ν) (d := d+1)
          (srcL := srcL) (srcR := srcR) (occ := occ) (maps := maps) (candidates := candidates)
          (histL := histL) (histR := histR) (masks := masks) (masksL := masksL) (masksR := masksR)
          (base := base) (bitBase := bitBase) (rowOut := rowOut) (work := work)
          av p shift left right q (prefixAt pres n) hk HLν HRν hw (by omega)
          hsrcL hsrcR hoffsetsL hoffsetsR hflatL hflatR hocc hmaps hcandidates hleft hright
          hmasks hmasksL hmasksR hstop hbits hrowOut hspace hword
          (fun j hj => (hkeep _ (by omega)).trans (hoccRead j hj)) hcoverν
          (fun i hi => (hkeep _ (by omega)).trans (hreadL i hi))
          (fun j hj => (hkeep _ (by omega)).trans (hreadR j hj)) hvaluesL hvaluesR ha htarget hcountWord).append [body 39 38]
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
            | refine Light.Ends.callToThen (hterminal _ (by omega)) ?_ ?_ ?_ ?_
            | refine Light.Ends.callToThen hterminal ?_ ?_ ?_ ?_);
          (on_goal -1 =>
              first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                      LightReportingTerminal.time]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [LightReportingTerminal.time] <;>
                    first
                    | omega
                    | ((ring_nf); (omega))));
          (on_goal -1 => omega);
          (on_goal -1 =>
              (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul,
                      LightReportingTerminal.time] <;>
                    omega)));
          (on_goal -1 =>
              ((rintro found ν₂ ⟨hfoundBool, hfound, hkeepTerminal⟩);
                (try with_unfolding_none refine Light.Ends.skip ?_)))
        have hprevRange : 0≤prev ∧ prev≤1 := by rcases hprevBool with hh | hh <;> omega
        have hfoundRange : 0≤found ∧ found≤1 := by rcases hfoundBool with hh | hh <;> omega
        have hwhole : Kept μ ν₂ masks := fun i hi => (hkeepTerminal i hi).trans (hkeep i hi)
        have hsum : (0 : ℤ)<prev+found ↔ Hit av p shift left right NL NR q k pres (n+1) := by
          rw [hit_succ]
          rw [show (0 : ℤ)<prev+found ↔ prev=1 ∨ found=1 by omega,hprev,hfound]
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
              Light.Ends.iteIffThen ((0 : ℤ) < prev + found) (fun hfoundSome => ?_)
                (fun hfoundNone => ?_) ?_ ?_);
          (on_goal -1 =>
              first
              |
                ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                      LightReportingTerminal.time]);
                  (first
                    | omega
                    | ((ring_nf); (omega))))
              | omega
              |
                (simp [LightReportingTerminal.time] <;>
                    first
                    | omega
                    | ((ring_nf); (omega))));
          (on_goal -1 =>
              (((try have := Light.Std.space_le (by assumption)));
                ((try have := Light.Std.const_le (by assumption)));
                (simp [Light.Limits.Addr, abs_le, -abs_mul,
                      LightReportingTerminal.time] <;>
                    omega)));
          (all_goals
              repeat
                with_unfolding_none
                  first
                  | refine Light.Ends.seqAssoc ?_
                  | refine Light.Ends.skipThen ?_)
        · have htrue := hsum.mp hfoundSome
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
                        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                        LightReportingTerminal.time]);
                    (first
                      | omega
                      | ((ring_nf); (omega))))
                | omega
                |
                  (simp [LightReportingTerminal.time] <;>
                      first
                      | omega
                      | ((ring_nf); (omega))));
            (on_goal -1 =>
                (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul,
                        LightReportingTerminal.time] <;>
                      omega)));
            (try with_unfolding_none refine Light.Ends.skip ?_)
          exact ⟨by simp,by simpa using htrue,hwhole⟩
        · have hfalse : ¬Hit av p shift left right NL NR q k pres (n+1) :=
            fun hh => hfoundNone (hsum.mpr hh)
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
                        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                        LightReportingTerminal.time]);
                    (first
                      | omega
                      | ((ring_nf); (omega))))
                | omega
                |
                  (simp [LightReportingTerminal.time] <;>
                      first
                      | omega
                      | ((ring_nf); (omega))));
            (on_goal -1 =>
                (((try have := Light.Std.space_le (by assumption)));
                  ((try have := Light.Std.const_le (by assumption)));
                  (simp [Light.Limits.Addr, abs_le, -abs_mul,
                        LightReportingTerminal.time] <;>
                      omega)));
            (try with_unfolding_none refine Light.Ends.skip ?_)
          exact ⟨by simp,by simp [hfalse],hwhole⟩
      · omega

end ThreeSum.LightReportingTerminalFrontier

end


theorem solution : ∀ {lim : Light.Limits} {μ : Nat → Int}
  {h J k srcL srcR offsetsL offsetsR flatL flatR NL NR occ maps candidates histL histR inL inR masks masksL masksR base
    bitBase rowOut work n d : Nat}
  (av : Int) (p : Nat) (shift : Int) (left right : Nat → Int) (q : ThreeSum.GlobalEncoding.GlobalOutput h J)
  (pres :
    List.{0}
      (List.{0}
        (Finset.{0}
          (Fin
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))))
  (hk : @LE.le.{0} Nat instLENat k J)
  (hn :
    @LE.le.{0} Nat instLENat n
      (@List.length.{0}
        (List.{0}
          (Finset.{0}
            (Fin
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
        pres))
  (HL :
    ThreeSum.SourceBuckets.Stored μ
      (fun (i : Nat) =>
        ThreeSum.LightSourceResidues.key p (ThreeSum.BlockSourceEncoding.modulus h J)
          (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) (left i))
      NL (ThreeSum.BlockSourceEncoding.modulus h J) offsetsL flatL)
  (HR :
    ThreeSum.SourceBuckets.Stored μ
      (fun (i : Nat) => ThreeSum.LightSourceResidues.key p (ThreeSum.BlockSourceEncoding.modulus h J) shift (right i))
      NR (ThreeSum.BlockSourceEncoding.modulus h J) offsetsR flatR)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d n)
            (ThreeSum.LightReportingTerminalMasks.count h J k))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
        (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
      lim.depth)
  (hsrcL : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcL NL) masks)
  (hsrcR : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcR NR) masks)
  (hoffsetsL :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offsetsL
          (ThreeSum.BlockSourceEncoding.modulus h J))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      masks)
  (hoffsetsR :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offsetsR
          (ThreeSum.BlockSourceEncoding.modulus h J))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      masks)
  (hflatL : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flatL NL) masks)
  (hflatR : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flatR NR) masks)
  (hocc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ J) masks)
  (hmaps :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
          (ThreeSum.GlobalEncoding.scheduleSize h)))
      masks)
  (hcandidates :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) candidates
        (ThreeSum.GlobalEncoding.scheduleSize h))
      masks)
  (hleft :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histL
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.LightLocalCoverSchedule.rows h)
          (ThreeSum.LocalCoverBounds.localPrime h)))
      masks)
  (hright :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histR
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.LightLocalCoverSchedule.rows h)
          (ThreeSum.LocalCoverBounds.localPrime h)))
      masks)
  (hinL :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) inL
        (@List.length.{0}
          (List.{0}
            (Finset.{0}
              (Fin
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
          pres))
      masks)
  (hinR :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) inR
        (@List.length.{0}
          (List.{0}
            (Finset.{0}
              (Fin
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
          pres))
      masks)
  (hmasks :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks
        (ThreeSum.LightReportingTerminalMasks.count h J k))
      masksL)
  (hmasksL :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masksL
        (ThreeSum.LightReportingTerminalMasks.count h J k))
      masksR)
  (hmasksR :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masksR
        (ThreeSum.LightReportingTerminalMasks.count h J k))
      base)
  (hstop :
    @LE.le.{0} Nat instLENat
      (ThreeSum.LightReportingTerminalPreparation.stop base
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
        (ThreeSum.LightReportingTerminalMasks.count h J k))
      bitBase)
  (hbits :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bitBase
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
      rowOut)
  (hrowOut :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rowOut
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      work)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightReportingTerminal.space work h J) lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightReportingTerminal.word h J)) lim.word)
  (hoccRead :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j J →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ j))
          (@Nat.cast.{0} Int instNatCastInt
            (@ThreeSum.BlockCoefficientRows.occurrenceIndices h J (@ThreeSum.BlockEncoding.outputOccurrences h J q) j)))
  (hcover : ThreeSum.BlockSourceCoverInput.Input μ h maps candidates histL histR)
  (hreadL :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i NL →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcL i)) (left i))
  (hreadR :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NR →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcR j)) (right j))
  (hreadInL :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i
          (@List.length.{0}
            (List.{0}
              (Finset.{0}
                (Fin
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
            pres) →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) inL i))
          (@Nat.cast.{0} Int instNatCastInt
            (@ThreeSum.SubsetAddress.subsetMask
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
              (@ThreeSum.BlockIndexedQuery.leftPrefix J
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                k
                (@ThreeSum.StoredReporting.prefixRows J
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                  (@ThreeSum.ReportingHostTerminalFrontier.prefixAt h pres i))))))
  (hreadInR :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i
          (@List.length.{0}
            (List.{0}
              (Finset.{0}
                (Fin
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
            pres) →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) inR i))
          (@Nat.cast.{0} Int instNatCastInt
            (@ThreeSum.SubsetAddress.subsetMask
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
              (@ThreeSum.BlockIndexedQuery.rightPrefix J
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                k (@ThreeSum.BlockForced.outputRows h J q)
                (@ThreeSum.StoredReporting.prefixRows J
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                  (@ThreeSum.ReportingHostTerminalFrontier.prefixAt h pres i))))))
  (hvaluesL :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i NL →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (left i)) lim.word)
  (hvaluesR :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NR →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (right j)) lim.word)
  (ha : @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup av) lim.word)
  (htarget :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i NL →
        @LE.le.{0} Int Int.instLEInt
          (@abs.{0} Int instLatticeInt Int.instAddGroup
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) av (left i)))
          lim.word)
  (hcountWord :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) NL NR))
      lim.word),
  Light.Meets lim ThreeSum.LightReportingTerminalFrontier.program
    (@OfNat.ofNat.{0} Nat (nat_lit 39) (instOfNatNat (nat_lit 39))) d
    (@List.cons.{0} Int av
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcL)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcR)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt offsetsL)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt flatL)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt offsetsR)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt flatR)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt NL)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt NR)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.BlockSourceEncoding.modulus h J))
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
                          (@List.cons.{0} Int
                            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                              (@OfNat.ofNat.{0} Int (nat_lit 512) (@instOfNat (nat_lit 512)))
                              (@Nat.cast.{0} Int instNatCastInt h))
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h)
                              (@List.cons.{0} Int
                                (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LocalCoverBounds.localPrime h))
                                (@List.cons.{0} Int
                                  (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LocalCoverBounds.localBucketCap h))
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt occ)
                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maps)
                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt candidates)
                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt histL)
                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt histR)
                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt k)
                                              (@List.cons.{0} Int
                                                (@Nat.cast.{0} Int instNatCastInt
                                                  (@ThreeSum.SubsetAddress.subsetMask
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                          (instOfNatNat (nat_lit 512)))
                                                        h))
                                                    (@ThreeSum.BlockIndexedQuery.querySet J
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 512)
                                                          (instOfNatNat (nat_lit 512)))
                                                        h)
                                                      k (@ThreeSum.BlockForced.outputRows h J q))))
                                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt inL)
                                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt inR)
                                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt masks)
                                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt masksL)
                                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt masksR)
                                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt base)
                                                            (@List.cons.{0} Int
                                                              (@Nat.cast.{0} Int instNatCastInt bitBase)
                                                              (@List.cons.{0} Int
                                                                (@Nat.cast.{0} Int instNatCastInt rowOut)
                                                                (@List.cons.{0} Int
                                                                  (@Nat.cast.{0} Int instNatCastInt work)
                                                                  (@List.cons.{0} Int
                                                                    (@Nat.cast.{0} Int instNatCastInt n)
                                                                    (@List.nil.{0} Int)))))))))))))))))))))))))))))))))
    μ (@ThreeSum.ReportingHostTerminalFrontier.time h J p shift left right NL NR q k pres n)
    fun (r : Int) (ν : Nat → Int) =>
    And
      (Or (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      (And
        (Iff (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@ThreeSum.ReportingHostTerminalFrontier.Hit h J av p shift left right NL NR q k pres n))
        (Light.Kept μ ν masks)) := by
  exact @ThreeSum.LightReportingTerminalFrontier.program_meets_sourceProof

#print axioms solution
