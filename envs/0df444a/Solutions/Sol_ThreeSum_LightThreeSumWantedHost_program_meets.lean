-- Prove2me | solution 1 for ThreeSum.LightThreeSumWantedHost.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:26:33.363259+00:00
-- url     : https://prove2.me/submissions/2578e4a7-3300-49b6-8e7c-33d256cacbdc

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
import Mathlib.Data.Int.Cast.Lemmas
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
import Mathlib.Data.Nat.Cast.Order.Ring
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_EncodedColorParameterData_reads
import Theorems.Thm_ThreeSum_EncodedColorPipelineData_ordered


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async true
namespace Light
end Light
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverMetadata
end ThreeSum.LightLocalCoverMetadata
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankData
end ThreeSum.SharedReportingBankData
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows
namespace ThreeSum.ThreeSumReportingSetupData
end ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum.ThreeSumWantedHostData
end ThreeSum.ThreeSumWantedHostData
namespace ThreeSumApsp
end ThreeSumApsp

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
                                                        ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                                                              hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce hrec
                                                              howner hval hnB hnC hGA hGB hGC hnword hJword hhword hKword hgword
                                                              hMword hlword hsword hRword hNword hReq hownerZ hRsum hBC0 hAB0
                                                              hAC0);
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
                                                        ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                                                              hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce hrec
                                                              howner hval hnB hnC hGA hGB hGC hnword hJword hhword hKword hgword
                                                              hMword hlword hsword hRword hNword hReq hownerZ hRsum hBC0 hAB0
                                                              hAC0);
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
                                                                                                              ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                                                                                                                    hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce hrec
                                                                                                                    howner hval hnB hnC hGA hGB hGC hnword hJword hhword hKword hgword
                                                                                                                    hMword hlword hsword hRword hNword hReq hownerZ hRsum hBC0 hAB0
                                                                                                                    hAC0);
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
              ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                    hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce hrec
                    howner hval hnB hnC hGA hGB hGC hnword hJword hhword hKword hgword
                    hMword hlword hsword hRword hNword hReq hownerZ hRsum hBC0 hAB0
                    hAC0);
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
              ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                    hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce hrec
                    howner hval hnB hnC hGA hGB hGC hnword hJword hhword hKword hgword
                    hMword hlword hsword hRword hNword hReq hownerZ hRsum hBC0 hAB0
                    hAC0);
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



























































































































/-- Reading a cell of a segment of natural numbers. -/
theorem SegN.read {l : List ℕ} (h : SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = ((l.getD i 0 : ℕ) : ℤ) := by
  rw [h i (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]




































































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
# The exact physical band-owner record order

There is one four-cell record for every owner-table cell, in BC, AB, AC
rectangle order. A zero flag is a lookup miss. Successful records retain
their physical owner slot even when several owners produce the same triple.
-/

namespace ThreeSum.BandCandidateRows

open BandEnumeration

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000



















































theorem rect_length (m n : ℕ) (F : ℕ → ℕ → Record) : (rect m n F).length=m*n := by
  simp [rect,List.length_flatMap]

theorem records_length (A B C : Family) :
    (records A B C).length=LightBandEnumeration.count A.size B.size C.size := by
  simp only [records,List.length_append,rect_length,LightBandEnumeration.count]
  omega


















































































































































end ThreeSum.BandCandidateRows

end

section


/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition





theorem size_le (n g : ℕ) : size n g ≤ n := by
  unfold size
  split_ifs with h
  · omega
  · have hdiv := Nat.div_le_self (n-1) g
    omega

theorem size_mono {n m g : ℕ} (h : n ≤ m) : size n g ≤ size m g := by
  by_cases hn : n = 0
  · simp [size,hn]
  · have hm : m ≠ 0 := by omega
    have hd := Nat.div_le_div_right (c := g) (show n-1 ≤ m-1 by omega)
    simp only [size,if_neg hn,if_neg hm]
    omega

































theorem length_le (n g i : ℕ) : stop n g i-start g i ≤ g := by
  have hle : stop n g i ≤ (i+1)*g := min_le_right _ _
  unfold start
  simp only [Nat.add_mul,Nat.one_mul] at hle
  omega


















































end ThreeSum.BandPartition

end

section


/-!
# Exact A-value incidences of the physical band-owner catalog

Each successful owner contributes only its A band. Labels retain the
physical owner slot and the coordinate in the retained sorted A array.
Equal values and equal triples in different owner slots remain distinct.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows BandEnumeration BandPartition

set_option maxHeartbeats 1600000
set_option maxRecDepth 7000





























theorem row_length (n g owner : ℕ) (r : Record) :
    (row n g owner r).length=if r.flag=1 then bandLength n g r.a else 0 := by
  unfold row
  split_ifs <;> simp

theorem row_length_le (n g owner : ℕ) (r : Record) : (row n g owner r).length ≤ g := by
  rw [row_length]
  split_ifs
  · exact BandPartition.length_le n g r.a
  · omega










theorem firstRows_succ (n g : ℕ) (rs : List Record) (i : ℕ) :
    firstRows n g rs (i+1)=firstRows n g rs i++row n g i (rs.getD i default) := by
  simp only [firstRows,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]

@[simp] theorem count_zero (n g : ℕ) (rs : List Record) : count n g rs 0=0 := rfl

theorem count_succ (n g : ℕ) (rs : List Record) (i : ℕ) :
    count n g rs (i+1)=count n g rs i+(row n g i (rs.getD i default)).length := by
  simp only [count,firstRows_succ,List.length_append]







theorem count_bound (n g : ℕ) (rs : List Record) (i : ℕ) : count n g rs i ≤ g*i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [count_succ]
    have hh := row_length_le n g i (rs.getD i default)
    nlinarith

theorem items_length_le (n g : ℕ) (rs : List Record) : (items n g rs).length ≤ g*rs.length :=
  count_bound n g rs rs.length

























































































end ThreeSum.BandRawA

end

section


/-!
# Stable extraction of one color class from the original signed array

The program reads stored colors and original values. It writes a length
header followed by exactly the selected values, optionally negated. Repeated
values are preserved; deduplication belongs to the later normalization pass.
-/

namespace ThreeSum.LightClassFilter

open Light

set_option maxHeartbeats 1200000












theorem items_length_le (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) :
    (items x color want scale n).length ≤ n := by
  simpa only [items,List.length_map,List.length_range] using
    List.length_filter_le (p := fun i => decide (color i = want)) (l := List.range n)

























variable {lim : Limits} {P : Program} {d : ℕ}























































































end ThreeSum.LightClassFilter

end

section


/-!
# Exact original-position semantics of the constructed color-class lists

The machine keeps repeated values within a class and negates the third
class. The list membership witnesses are original positions. Any binary
width large enough for the indices suffices for the deterministic family.
-/

namespace ThreeSum.ColorClassLists

open LightClassFilter




































theorem length_classList_le {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) : (classList p x c scale).length ≤ n :=
  items_length_le ..



































































end ThreeSum.ColorClassLists

end

section


/-! # One compact retained layout for a selected color -/

namespace ThreeSum.EncodedColorLayout





















theorem normalized_ends_before_count (free n g : ℕ) :
    av free n+n ≤ normalizedEnd free n g ∧ ae free n+2+2*n ≤ normalizedEnd free n g ∧
    bv free n+n ≤ normalizedEnd free n g ∧ be free n+2+2*n ≤ normalizedEnd free n g ∧
    cv free n+n ≤ normalizedEnd free n g ∧ ce free n+2+2*n ≤ normalizedEnd free n g ∧
    tables free n+ColorBandBounds.count n g ≤ normalizedEnd free n g ∧
    rec free n g+4*ColorBandBounds.count n g ≤ normalizedEnd free n g := by
  unfold normalizedEnd LightBandRawA.space LightBandRawA.positionBase LightBandRawA.ownerBase
    LightBandRawA.capacity vals rec tables ce cv be bv ae av
  omega





















theorem prime_le_cover (free n g M y : ℕ) : prime free n g+6 ≤ cover free n g M y := by
  unfold cover EncodedColorPrimeData.nextFree EncodedColorPrimeData.prefixBase EncodedColorPrimeData.poolBase
  omega

theorem normalized_ends_cover (free n g M y : ℕ) :
    av free n+n ≤ cover free n g M y ∧ ae free n+2+2*n ≤ cover free n g M y ∧
    bv free n+n ≤ cover free n g M y ∧ be free n+2+2*n ≤ cover free n g M y ∧
    cv free n+n ≤ cover free n g M y ∧ ce free n+2+2*n ≤ cover free n g M y ∧
    tables free n+ColorBandBounds.count n g ≤ cover free n g M y ∧
    rec free n g+4*ColorBandBounds.count n g ≤ cover free n g M y ∧
    LightBandRawA.space (vals free n g) (ColorBandBounds.count n g) g ≤ cover free n g M y := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := normalized_ends_before_count free n g
  have h := prime_le_cover free n g M y
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ normalizedEnd free n g ≤ _
  unfold prime at h
  omega

end ThreeSum.EncodedColorLayout

end

section


/-! # Retained local-cover tables survive reuse of the returned free region -/

namespace ThreeSum.LightLocalCoverRetention

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMetadata

set_option maxHeartbeats 1000000

theorem base_le_nextFree (base h : ℕ) : base ≤ nextFree base h := by
  unfold nextFree scheduleMaps work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr
    LightCoverGreedy.total
  omega




















































end ThreeSum.LightLocalCoverRetention

end

section


/-!
# The retained cover, output layers, and exact global key array

This bundle is produced by the actual cover/key host and remains valid when
later phases use its computed next free address. In particular the output
index decoder can read the original layer masks without reconstructing them.
-/

namespace ThreeSum.LightCoverKeyData

open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000







theorem layer_end_le_header (free h J : ℕ) :
    LightCoverKeys.afterCover free h+outputCount (512*h) h ≤ LightCoverKeys.keyHeader free h J := by
  unfold LightCoverKeys.keyHeader LightGlobalKeys.scratch
  omega

theorem afterCover_le_keyEnd (free h J : ℕ) : LightCoverKeys.afterCover free h ≤ keyEnd free h J := by
  have hh := layer_end_le_header free h J
  unfold keyEnd
  omega






















































end ThreeSum.LightCoverKeyData

end

section


/-! # Concrete source inputs from the retained normalization and wanted outputs -/

namespace ThreeSum.SourceFiniteInputs

open Light GlobalEncoding LocalCoverBounds LightLocalCoverLayout LightLocalCoverSchedule



























theorem prepared_headers {μ : ℕ → ℤ} {values endpoints g : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (H : LightBandPreprocessing.Represents μ values endpoints g hg original L hs) :
    μ endpoints=(L.length : ℤ) ∧ μ (endpoints+1)=(BandPartition.size L.length g : ℤ) :=
  ⟨H.2.2.2.1,H.2.2.2.2.1⟩



























end ThreeSum.SourceFiniteInputs

end

section


/-! # Actual finite budgets of the retained common-prime stage -/

namespace ThreeSum.EncodedColorPrimeCosts

open Light Scales BandScales CostLedger ArithmeticStageBounds
















theorem count_mono {nA nB nC nA' nB' nC' g : ℕ} (ha : nA ≤ nA') (hb : nB ≤ nB') (hc : nC ≤ nC') :
    LightEncodedColorPrime.count nA nB nC g ≤ LightEncodedColorPrime.count nA' nB' nC' g := by
  have a := BandPartition.size_mono (g := g) ha
  have b := BandPartition.size_mono (g := g) hb
  have c := BandPartition.size_mono (g := g) hc
  unfold LightEncodedColorPrime.count
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul b c) (Nat.mul_le_mul a b)) (Nat.mul_le_mul a c)






























































end ThreeSum.EncodedColorPrimeCosts

end

section


/-! # Retained normalized pointers and the actual incidence-count cell -/

namespace ThreeSum.EncodedColorNormalizedData

open Light Scales BandScales ColorClassLists BandRawA EncodedColorLayout
















theorem records_length_le {A B C : List ℤ} {g n : ℕ} {hg : 0 < g}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (ha : A.length ≤ n) (hb : B.length ≤ n) (hc : C.length ≤ n) :
    (sortedRecords A B C g hg hsA hsB hsC).length ≤ ColorBandBounds.count n g := by
  have h := EncodedColorPrimeCosts.count_mono (g := g) ha hb hc
  have hright : LightEncodedColorPrime.count n n n g=ColorBandBounds.count n g := by
    unfold LightEncodedColorPrime.count ColorBandBounds.count
    ring
  rw [hright] at h
  simp only [sortedRecords, BandCandidateRows.records_length]
  exact h














theorem heads_read {μ : ℕ → ℤ} {free n g : ℕ} (H : Seg μ free (normalizedHeads free n g)) :
    μ free=(av free n : ℤ) ∧ μ (free+1)=(ae free n : ℤ) ∧
    μ (free+2)=(bv free n : ℤ) ∧ μ (free+3)=(be free n : ℤ) ∧
    μ (free+4)=(cv free n : ℤ) ∧ μ (free+5)=(ce free n : ℤ) ∧
    μ (free+6)=(rec free n g : ℤ) ∧ μ (free+7)=(vals free n g : ℤ) := by
  have h (i : ℕ) (hi : i < 8) := H.getD (i := i) (by simpa [normalizedHeads] using hi) 0
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [normalizedHeads] using h 0 (by omega)
  · simpa [normalizedHeads] using h 1 (by omega)
  · simpa [normalizedHeads] using h 2 (by omega)
  · simpa [normalizedHeads] using h 3 (by omega)
  · simpa [normalizedHeads] using h 4 (by omega)
  · simpa [normalizedHeads] using h 5 (by omega)
  · simpa [normalizedHeads] using h 6 (by omega)
  · simpa [normalizedHeads] using h 7 (by omega)

end ThreeSum.EncodedColorNormalizedData

end

section


/-! # Keep the complete selected-color payload while later stages extend memory -/

namespace ThreeSum.EncodedColorPipelineData

open Light Scales BandScales ColorClassLists EncodedColorNormalizedData

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000

theorem Stored.heads_read {μ : ℕ → ℤ} {free n : ℕ} {color : Coloring.Parameter (inputBits n+1)}
    {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : Stored μ free n color x A B C hsA hsB hsC) :
    let out := finish free n A B C hsA hsB hsC
    μ out=(EncodedColorLayout.prime free n (bandSize n) : ℤ) ∧
    μ (out+1)=(coverBase free n : ℤ) ∧
    μ (out+2)=(wantedHeader free n (incidences n A B C hsA hsB hsC).length : ℤ) ∧
    μ (out+3)=(controls free n A B C hsA hsB hsC : ℤ) ∧
    μ (out+4)=(bankHeader free n A B C hsA hsB hsC : ℤ) ∧
    μ (out+5)=(out+8 : ℕ) ∧
    μ (out+6)=((incidences n A B C hsA hsB hsC).length : ℤ) ∧
    μ (out+7)=(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 0) (by simp [values,LightEncodedColorResult.values]) 0
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 1) (by simp [values,LightEncodedColorResult.values]) 0
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 2) (by simp [values,LightEncodedColorResult.values]) 0
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 3) (by simp [values,LightEncodedColorResult.values]) 0
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 4) (by simp [values,LightEncodedColorResult.values]) 0
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 5) (by simp [values,LightEncodedColorResult.values]) 0
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 6) (by simp [values,LightEncodedColorResult.values]) 0
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 7) (by simp [values,LightEncodedColorResult.values]) 0














































end ThreeSum.EncodedColorPipelineData

end

section


/-!
# Actual encoding-output masses fit the uniform reporting budgets

Both inequalities come from the retained pipeline payload. The wanted
count includes all physical A occurrences and all three lifts; the false
score uses the very common modulus selected from the original normalized
arrays. No input-dependent counting or prime-quality premise is assumed.
The explicit numerical divisor premise is discharged eventually, uniformly
before the input arrays are quantified.
-/

namespace ThreeSum.ThreeSumColorBudgets

open Light Scales BandScales CostLedger GlobalEncoding LocalCoverBounds
open ColorClassLists EncodedColorNormalizedData

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000


















variable {μ : ℕ → ℤ} {free n : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n → ℤ}
    {A B C : List ℤ} {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

theorem normalized_lengths (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    A.length ≤ n ∧ B.length ≤ n ∧ C.length ≤ n :=
  ⟨H.normalized.2.1.2.1.trans (length_classList_le color x 0 1),
    H.normalized.2.2.1.2.1.trans (length_classList_le color x 1 1),
    H.normalized.2.2.2.1.2.1.trans (length_classList_le color x 2 (-1))⟩


























































































open Filter













end ThreeSum.ThreeSumColorBudgets

end

section


/-! # A retained header for the complete shared reporting catalog bank -/

namespace ThreeSum.SharedReportingBankHeader

open Light GlobalEncoding SharedReportingBankRows SharedReportingBankLevels
open SharedReportingBankLayout SharedReportingBankData

set_option maxHeartbeats 1900000













theorem records_le_payload (free h J NB NC g : ℕ) :
    records free ≤ payload free h J NB NC g := Nat.le_add_right _ _
theorem payload_le_finish (free h J NB NC g : ℕ) :
    payload free h J NB NC g ≤ finish free h J NB NC g := Nat.le_add_right _ _












































































end ThreeSum.SharedReportingBankHeader

end

section


/-! # Exact retained addresses for reporting one encoded original color -/

namespace ThreeSum.ThreeSumReportingSetupData

open Light Scales BandScales EncodedColorNormalizedData

attribute [local instance] _root_.ThreeSum.ThreeSumReportingSetupData.instNeZeroNatRadix
































theorem report_le_counter (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    reportBase free n A B C hsA hsB hsC+9 ≤ counter free n A B C hsA hsB hsC :=
  (SharedReportingBankHeader.records_le_payload ..).trans
    (SharedReportingBankHeader.payload_le_finish ..)

theorem prefix_le_report (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    free+8 ≤ reportBase free n A B C hsA hsB hsC ∧
    EncodedColorPipelineData.coverBase free n ≤ reportBase free n A B C hsA hsB hsC := by
  obtain ⟨_,hf,hc,_,hs,_⟩ := EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  unfold reportBase
  omega

theorem cover_end_le_report (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    LightCoverKeyData.keyEnd (EncodedColorPipelineData.coverBase free n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) ≤ reportBase free n A B C hsA hsB hsC := by
  obtain ⟨_,_,_,hw,hs,_⟩ := EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  have he : EncodedColorPipelineData.wantedHeader free n (incidences n A B C hsA hsB hsC).length=
      LightCoverKeyData.keyEnd (EncodedColorPipelineData.coverBase free n)
        (microHalf (inputBits n)) (blockCount (inputBits n))+3*(incidences n A B C hsA hsB hsC).length := rfl
  unfold reportBase
  omega











end ThreeSum.ThreeSumReportingSetupData

end

section


/-! # The wanted consumer's configuration from the actual retained color payload -/

namespace ThreeSum.ThreeSumWantedHostData

open Light Scales BandScales ThreeSumReportingSetupData EncodedColorNormalizedData

local instance (n : ℕ) : NeZero (radix n) := ⟨Nat.ne_of_gt (radix_pos n)⟩













































theorem recordCount_eq (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    recordCount n A B C hsA hsB hsC=
      BandPartition.size B.length (bandSize n)*BandPartition.size C.length (bandSize n)+
      BandPartition.size A.length (bandSize n)*BandPartition.size B.length (bandSize n)+
      BandPartition.size A.length (bandSize n)*BandPartition.size C.length (bandSize n) := by
  simp only [recordCount,BandRawA.sortedRecords,BandCandidateRows.records_length]
  rfl








theorem pairs_read {μ : ℕ→ℤ} {free n : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    μ (EncodedColorPipelineData.wantedHeader free n (incidences n A B C hsA hsB hsC).length+1)=
      ((config free n A B C hsA hsB hsC).pairs : ℤ) := H.wanted.2.1

end ThreeSum.ThreeSumWantedHostData

end

section


/-!
# Load the retained color headers and execute the actual wanted scan

All controls passed to the fixed153 scan are read from the initialized
parameter, normalization, encoding and reporting headers. The raw-owner
array is located using the actual three band counts stored by normalization.
-/

namespace ThreeSum.LightThreeSumWantedHost

open Light Scales BandScales ThreeSumReportingSetupData ThreeSumWantedHostData
open BandPartition EncodedColorNormalizedData

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

local instance (n : ℕ) : NeZero (radix n) := ⟨Nat.ne_of_gt (radix_pos n)⟩

















































end ThreeSum.LightThreeSumWantedHost

end

section


/-! # Small independent header and numeric facts used by the concrete loader -/

namespace ThreeSum.LightThreeSumWantedHost

open Light Scales BandScales

set_option maxHeartbeats 1200000

theorem word_bounds (n : ℕ) :
    n≤word n ∧ blockCount (inputBits n)≤word n ∧ microHalf (inputBits n)≤word n ∧
    LightSwitchDepth.depth (blockCount (inputBits n))+1≤word n ∧ bandSize n≤word n ∧
    radix n≤word n ∧ OutputDecodeRecords.layerCount (microHalf (inputBits n))≤word n ∧
    GlobalEncoding.scheduleSize (microHalf (inputBits n))≤word n ∧
    ColorBandBounds.count n (bandSize n)≤word n ∧
    bandSize n*ColorBandBounds.count n (bandSize n)≤word n := by
  unfold word
  omega

theorem cover_header_reads {μ : ℕ→ℤ} {cover h J : ℕ}
    (H : LightCoverKeyData.Stored μ cover h J) :
    μ cover=(OutputDecodeRecords.layerCount h : ℤ) ∧
    μ (cover+10)=(GlobalEncoding.scheduleSize h : ℤ) ∧
    μ (cover+18)=(LightCoverKeys.afterCover cover h : ℤ) := by
  have Hread (i : ℕ) (hi : i<20) := H.header.getD (i := i)
    (by simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      LightLocalCoverMetadata.values] using hi) 0
  refine ⟨?_,?_,?_⟩
  · simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      OutputDecodeRecords.layerCount] using Hread 0 (by omega)
  · simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      LightLocalCoverMetadata.values] using Hread 10 (by omega)
  · simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      LightLocalCoverMetadata.values,LightCoverKeys.afterCover] using Hread 18 (by omega)

theorem report_level_read {μ : ℕ→ℤ} {report h J NB NC g : ℕ} {fB fC : ℕ→ℤ} {p shift : ℤ}
    (H : SharedReportingBankHeader.Stored μ report h J NB NC g fB fC p shift) :
    μ (report+2)=((LightSwitchDepth.depth J+1 : ℕ) : ℤ) := by
  simpa only [SharedReportingBankHeader.header,List.getD_cons_zero,List.getD_cons_succ,
    SharedReportingBankHeader.levels] using H.heads.read (i := 2)
      (by simp [SharedReportingBankHeader.header])

end ThreeSum.LightThreeSumWantedHost

end

section


namespace ThreeSum.LightThreeSumWantedHost

open Light Scales BandScales ThreeSumReportingSetupData ThreeSumWantedHostData
open BandPartition EncodedColorNormalizedData

set_option maxHeartbeats 5000000
set_option maxRecDepth 20000



private theorem natAddToNat (a b : ℕ) : ((a : ℤ)+(b : ℤ)).toNat=a+b := by omega

/- The execution lemma deliberately has only numeric controls.  Keeping the
   normalized arrays and source-bank definitions out of this proof avoids
   repeatedly reducing them while checking every individual header read. -/
private theorem header_meets {lim : Limits} {d T : ℕ} {μ : ℕ→ℤ}
    {n params free out ctr report cover controls bank ae bv be cv ce vals recs : ℕ}
    {h J K g R N wanted cnt pairs layers schedule masks owners M NB NC gA gB gC : ℕ}
    {Q : ℤ→(ℕ→ℤ)→Prop}
    (hparams : params+19≤free) (hw : (lim.space : ℤ)≤lim.word)
    (hd : d<lim.depth) (hspace : ctr+50≤lim.space)
    (hreport : report+9≤ctr) (hout : out+8=report) (hfree : free+8≤report)
    (hcover : cover≤report) (hwanted : wanted+4≤controls)
    (hcontrols : controls+3≤out) (hbank : bank+5≤out)
    (hcover20 : cover+20≤masks) (hmasks : masks≤report)
    (hpairs : pairs+2*cnt=controls)
    (hae : ae+2≤cover) (hbv : bv+NB≤cover) (hbe : be+2≤cover)
    (hcv : cv+NC≤cover) (hce : ce+2≤cover) (hrec : recs≤cover)
    (howner : owners≤cover) (hval : vals≤cover)
    (hnB : NB≤n) (hnC : NC≤n) (hGA : gA≤n) (hGB : gB≤n) (hGC : gC≤n)
    (hnword : (n : ℤ)≤lim.word) (hJword : (J : ℤ)≤lim.word)
    (hhword : (h : ℤ)≤lim.word) (hKword : ((K+1 : ℕ) : ℤ)≤lim.word)
    (hgword : (g : ℤ)≤lim.word) (hMword : (M : ℤ)≤lim.word)
    (hlword : (layers : ℤ)≤lim.word) (hsword : (schedule : ℤ)≤lim.word)
    (hRword : (R : ℤ)≤lim.word) (hNword : (N : ℤ)≤lim.word)
    (hReq : R=gB*gC+gA*gB+gA*gC)
    (hownerZ : (vals : ℤ)+(g : ℤ)*(R : ℤ)=(owners : ℤ))
    (readCover : μ (out+1)=(cover : ℤ)) (readWanted : μ (out+2)=(wanted : ℤ))
    (readControls : μ (out+3)=(controls : ℤ)) (readBank : μ (out+4)=(bank : ℤ))
    (readN : μ (out+6)=(N : ℤ)) (readAE : μ (free+1)=(ae : ℤ))
    (readB : μ (free+2)=(bv : ℤ)) (readBE : μ (free+3)=(be : ℤ))
    (readC : μ (free+4)=(cv : ℤ)) (readCE : μ (free+5)=(ce : ℤ))
    (readRecs : μ (free+6)=(recs : ℤ)) (readVals : μ (free+7)=(vals : ℤ))
    (readH : μ (params+1)=(h : ℤ)) (readJ : μ (params+3)=(J : ℤ))
    (readM : μ (params+14)=(M : ℤ)) (readG : μ (params+17)=(g : ℤ))
    (readGA : μ (ae+1)=(gA : ℤ)) (readGB : μ (be+1)=(gB : ℤ))
    (readGC : μ (ce+1)=(gC : ℤ)) (readNB : μ be=(NB : ℤ))
    (readNC : μ ce=(NC : ℤ)) (readCount : μ wanted=(cnt : ℤ))
    (readPairs : μ (wanted+1)=(pairs : ℤ))
    (readLevels : μ (report+2)=((K+1 : ℕ) : ℤ))
    (readLayers : μ cover=(layers : ℤ)) (readSchedule : μ (cover+10)=(schedule : ℤ))
    (readMasks : μ (cover+18)=(masks : ℤ))
    (hscan : Meets lim LightReportingWantedScan.program 152 (d+1)
      [cnt,(ctr+4 : ℕ),J,h,K,N,NB,NC,cover,ctr,pairs,layers,schedule,masks,vals,owners,recs,
        (controls+3 : ℕ),bank,bv,cv,report,M] μ T Q) :
    Meets lim program 153 d [n,params,free,out,ctr] μ (T+4000) Q := by
  have hRsum : (gB : ℤ)*(gC : ℤ)+(gA : ℤ)*(gB : ℤ)+(gA : ℤ)*(gC : ℤ)≤lim.word := by
    simpa only [hReq,Nat.cast_add,Nat.cast_mul] using hRword
  have hBC0 : (0 : ℤ)≤(gB : ℤ)*(gC : ℤ) := by positivity
  have hAB0 : (0 : ℤ)≤(gA : ℤ)*(gB : ℤ) := by positivity
  have hAC0 : (0 : ℤ)≤(gA : ℤ)*(gC : ℤ) := by positivity
  have out1 : ((out : ℤ)+1).toNat=out+1 := natAddToNat out 1
  have out2 : ((out : ℤ)+2).toNat=out+2 := natAddToNat out 2
  have out3 : ((out : ℤ)+3).toNat=out+3 := natAddToNat out 3
  have out4 : ((out : ℤ)+4).toNat=out+4 := natAddToNat out 4
  have out6 : ((out : ℤ)+6).toNat=out+6 := natAddToNat out 6
  have free1 : ((free : ℤ)+1).toNat=free+1 := natAddToNat free 1
  have free2 : ((free : ℤ)+2).toNat=free+2 := natAddToNat free 2
  have free3 : ((free : ℤ)+3).toNat=free+3 := natAddToNat free 3
  have free4 : ((free : ℤ)+4).toNat=free+4 := natAddToNat free 4
  have free5 : ((free : ℤ)+5).toNat=free+5 := natAddToNat free 5
  have free6 : ((free : ℤ)+6).toNat=free+6 := natAddToNat free 6
  have free7 : ((free : ℤ)+7).toNat=free+7 := natAddToNat free 7
  have par1 : ((params : ℤ)+1).toNat=params+1 := natAddToNat params 1
  have par3 : ((params : ℤ)+3).toNat=params+3 := natAddToNat params 3
  have par14 : ((params : ℤ)+14).toNat=params+14 := natAddToNat params 14
  have par17 : ((params : ℤ)+17).toNat=params+17 := natAddToNat params 17
  have report2 : ((report : ℤ)+2).toNat=report+2 := natAddToNat report 2
  have wanted1 : ((wanted : ℤ)+1).toNat=wanted+1 := natAddToNat wanted 1
  have cover10 : ((cover : ℤ)+10).toNat=cover+10 := natAddToNat cover 10
  have cover18 : ((cover : ℤ)+18).toNat=cover+18 := natAddToNat cover 18
  have ae1 : ((ae : ℤ)+1).toNat=ae+1 := natAddToNat ae 1
  have be1 : ((be : ℤ)+1).toNat=be+1 := natAddToNat be 1
  have ce1 : ((ce : ℤ)+1).toNat=ce+1 := natAddToNat ce 1
  apply Meets.of_body (p := 153) (by rfl : program[153]?=some (body 152))
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
    (refine Light.Ends.setToThen (ctr + 4 : ℕ) ?_ ?_ ?_);
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
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (J : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readJ,
                par3]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readJ, par3] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readJ, par3] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (h : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readH,
                par1]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readH, par1] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readH, par1] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (report : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hout]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hout] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hout] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (K + 1 : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                readLevels, report2]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readLevels, report2] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readLevels, report2] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (K : ℕ) ?_ ?_ ?_);
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
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (N : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readN,
                out6]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readN, out6] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readN, out6] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (ae : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readAE,
                free1]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readAE, free1] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readAE, free1] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (be : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readBE,
                free3]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readBE, free3] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readBE, free3] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (ce : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readCE,
                free5]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readCE, free5] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readCE, free5] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (NB : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                readNB]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readNB] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readNB] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (NC : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                readNC]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readNC] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readNC] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (cover : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                readCover, out1]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readCover, out1] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readCover, out1] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (wanted : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                readWanted, out2]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readWanted, out2] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readWanted, out2] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (cnt : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                readCount]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readCount] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readCount] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (pairs : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                readPairs, wanted1]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readPairs, wanted1] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readPairs, wanted1] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (layers : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                readLayers]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readLayers] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readLayers] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (schedule : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                readSchedule, cover10]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readSchedule, cover10] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readSchedule, cover10] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (masks : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                readMasks, cover18]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readMasks, cover18] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readMasks, cover18] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (vals : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                readVals, free7]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readVals, free7] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readVals, free7] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (recs : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                readRecs, free6]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readRecs, free6] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readRecs, free6] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (controls : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                readControls, out3]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readControls, out3] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readControls, out3] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (controls + 3 : ℕ) ?_ ?_ ?_);
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
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (bank : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                readBank, out4]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readBank, out4] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readBank, out4] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (bv : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readB,
                free2]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readB, free2] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readB, free2] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (cv : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readC,
                free4]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readC, free4] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readC, free4] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (M : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readM,
                par14]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readM, par14] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readM, par14] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (g : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readG,
                par17]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readG, par17] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readG, par17] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (gA : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readGA,
                ae1]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readGA, ae1] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readGA, ae1] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (gB : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readGB,
                be1]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readGB, be1] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readGB, be1] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (gC : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, readGC,
                ce1]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [readGC, ce1] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, readGC, ce1] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (R : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hReq]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hReq] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hReq] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
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
    (refine Light.Ends.setToThen (owners : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hownerZ]);
            (first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hownerZ] <;>
              first
              | ((clear * -); (omega))
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hownerZ] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
                  (omega))
              | omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  have hrun := hscan.append [body 152]
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
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;>
              first
              | assumption
              |
                ((clear * - hparams hw hspace hreport hout hfree hcover hwanted
                      hcontrols hbank hcover20 hmasks hpairs hae hbv hbe hcv hce
                      hrec howner hval hnB hnC hGA hGB hGC hnword hJword hhword
                      hKword hgword hMword hlword hsword hRword hNword hReq
                      hownerZ hRsum hBC0 hAB0 hAC0);
                  (omega))
              | omega)));
    (on_goal -1 =>
        ((rintro result ν hQ);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  exact hQ

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
theorem _root_.ThreeSum.LightThreeSumWantedHost.program_meets._proof_1_1 : ∀ {lim : Light.Limits} {d free n params : Nat} {A B C : List.{0} Int} {hsA : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) A} {hsB : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) B} {hsC : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) C} (hvals : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.EncodedColorLayout.vals free n (ThreeSum.BandScales.bandSize n)) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.BandScales.bandSize n) (ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n)))) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.BandScales.bandSize n) (ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n)))) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.BandScales.bandSize n) (ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n)))) (ThreeSum.EncodedColorPipelineData.coverBase free n)) (hh : @LE.le.{0} Nat instLENat (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.BandScales.bandSize n) (ThreeSum.ThreeSumWantedHostData.recordCount n A B C hsA hsB hsC)) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.BandScales.bandSize n) (ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n)))), Not (@LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.EncodedColorLayout.vals free n (ThreeSum.BandScales.bandSize n)) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.BandScales.bandSize n) (ThreeSum.ThreeSumWantedHostData.recordCount n A B C hsA hsB hsC))) (ThreeSum.EncodedColorPipelineData.coverBase free n)) → False :=
by
  intros
  first | omega | (solve | simp_all [abs_le]) | norm_num

theorem _root_.ThreeSum.LightThreeSumWantedHost.program_meets._proof_1_2 : ∀ {lim : Light.Limits} {d free n params : Nat} {A B C : List.{0} Int} {hsA : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) A} {hsB : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) B} {hsC : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) C} (howner : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.EncodedColorLayout.vals free n (ThreeSum.BandScales.bandSize n)) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.BandScales.bandSize n) (ThreeSum.ThreeSumWantedHostData.recordCount n A B C hsA hsB hsC))) (ThreeSum.EncodedColorPipelineData.coverBase free n)), Not (@LE.le.{0} Nat instLENat (ThreeSum.EncodedColorLayout.vals free n (ThreeSum.BandScales.bandSize n)) (ThreeSum.EncodedColorPipelineData.coverBase free n)) → False :=
by
  intros
  first | omega | (solve | simp_all [abs_le]) | norm_num

theorem _root_.ThreeSum.LightThreeSumWantedHost.program_meets_sourceProof : ∀ {lim : Light.Limits} {d T : Nat} {μ : Nat → Int} {free n params : Nat}
  {color :
    ThreeSum.Coloring.Parameter
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.Scales.inputBits n)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
  {x : Fin n → Int} {A B C : List.{0} Int}
  {hsA : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) A}
  {hsB : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) B}
  {hsC : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) C}
  {Q : Int → (Nat → Int) → Prop} (H : ThreeSum.ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
  (Hparams : Light.Seg μ params (ThreeSum.LightParameterInit.values n))
  (hparams :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) params
        (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19))))
      free)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd : @LT.lt.{0} Nat instLTNat d lim.depth)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC)
          (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n))))
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightThreeSumWantedHost.word n)) lim.word)
  (hscan :
    Light.Meets lim ThreeSum.LightReportingWantedScan.program
      (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (ThreeSum.LightReportingWantedDispatch.arguments (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC)
        (ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC))
      μ T Q),
  Light.Meets lim ThreeSum.LightThreeSumWantedHost.program
    (@OfNat.ofNat.{0} Nat (nat_lit 153) (instOfNatNat (nat_lit 153))) d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt params)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt free)
          (@List.cons.{0} Int
            (@Nat.cast.{0} Int instNatCastInt (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC))
            (@List.cons.{0} Int
              (@Nat.cast.{0} Int instNatCastInt (ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC))
              (@List.nil.{0} Int))))))
    μ
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) T
      (@OfNat.ofNat.{0} Nat (nat_lit 4000) (instOfNatNat (nat_lit 4000))))
    Q :=
fun {lim : Light.Limits} {d T : ℕ} {μ : ℕ → ℤ} {free n params : ℕ} {color : ThreeSum.Coloring.Parameter (ThreeSum.Scales.inputBits n + OfNat.ofNat (nat_lit 1))} {x : Fin n → ℤ} {A B C : List ℤ} {hsA : List.Pairwise (fun (x1 x2 : ℤ) => x1 < x2) A} {hsB : List.Pairwise (fun (x1 x2 : ℤ) => x1 < x2) B} {hsC : List.Pairwise (fun (x1 x2 : ℤ) => x1 < x2) C} {Q : ℤ → (ℕ → ℤ) → Prop} (H : ThreeSum.ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC) (Hparams : Light.Seg μ params (ThreeSum.LightParameterInit.values n)) (hparams : params + OfNat.ofNat (nat_lit 19) ≤ free) (hw : Nat.cast (Light.Limits.space lim) ≤ Light.Limits.word lim) (hd : d < Light.Limits.depth lim) (hspace : ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 50) + OfNat.ofNat (nat_lit 2) * ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n) ≤ Light.Limits.space lim) (hword : Nat.cast (ThreeSum.LightThreeSumWantedHost.word n) ≤ Light.Limits.word lim) (hscan : Light.Meets lim ThreeSum.LightReportingWantedScan.program (OfNat.ofNat (nat_lit 152)) (d + OfNat.ofNat (nat_lit 1)) (ThreeSum.LightReportingWantedDispatch.arguments (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC) (ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)) μ T Q) =>
  let out : ℕ := ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC;
  let ctr : ℕ := ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC;
  let report : ℕ := ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC;
  let cover : ℕ := ThreeSum.EncodedColorPipelineData.coverBase free n;
  let controls : ℕ := ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC;
  let bank : ℕ := ThreeSum.EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC;
  let ae : ℕ := ThreeSum.EncodedColorLayout.ae free n;
  let bv : ℕ := ThreeSum.EncodedColorLayout.bv free n;
  let be : ℕ := ThreeSum.EncodedColorLayout.be free n;
  let cv : ℕ := ThreeSum.EncodedColorLayout.cv free n;
  let ce : ℕ := ThreeSum.EncodedColorLayout.ce free n;
  let vals : ℕ := ThreeSum.EncodedColorLayout.vals free n (ThreeSum.BandScales.bandSize n);
  let recs : ℕ := ThreeSum.EncodedColorLayout.rec free n (ThreeSum.BandScales.bandSize n);
  let h : ℕ := ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n);
  let J : ℕ := ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n);
  let K : ℕ := ThreeSum.LightSwitchDepth.depth J;
  let g : ℕ := ThreeSum.BandScales.bandSize n;
  let R : ℕ := ThreeSum.ThreeSumWantedHostData.recordCount n A B C hsA hsB hsC;
  let N : ℕ := List.length (ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC);
  let wanted : ℕ := ThreeSum.EncodedColorPipelineData.wantedHeader free n N;
  let cnt : ℕ := ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC;
  let pairs : ℕ := ThreeSum.LightWantedSetup.pairBase wanted (OfNat.ofNat (nat_lit 3) * N) (ThreeSum.LightGuardedWanted.totalKeys h J) (ThreeSum.Scales.radix n);
  let layers : ℕ := ThreeSum.OutputDecodeRecords.layerCount h;
  let schedule : ℕ := ThreeSum.GlobalEncoding.scheduleSize h;
  let masks : ℕ := ThreeSum.LightCoverKeys.afterCover cover h;
  let owners : ℕ := ThreeSum.LightBandRawA.ownerBase vals R g;
  have hreport : ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 9) ≤ ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC := ThreeSum.ThreeSumReportingSetupData.report_le_counter free n A B C hsA hsB hsC;
  id
    (fun (hreport : report + OfNat.ofNat (nat_lit 9) ≤ ctr) =>
      have hout : out + OfNat.ofNat (nat_lit 8) = report := rfl;
      And.casesOn (ThreeSum.ThreeSumReportingSetupData.prefix_le_report free n A B C hsA hsB hsC) fun (hfree : free + OfNat.ofNat (nat_lit 8) ≤ ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC) (hcover : ThreeSum.EncodedColorPipelineData.coverBase free n ≤ ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC) =>
        id
          (fun (hfree : free + OfNat.ofNat (nat_lit 8) ≤ report) =>
            id
              (fun (hcover : cover ≤ report) =>
                And.casesOn (ThreeSum.EncodedColorPipelineData.ordered free n A B C hsA hsB hsC) fun (left : ThreeSum.EncodedColorLayout.prime free n (ThreeSum.BandScales.bandSize n) + OfNat.ofNat (nat_lit 6) ≤ ThreeSum.EncodedColorPipelineData.coverBase free n) (right : free + OfNat.ofNat (nat_lit 8) ≤ ThreeSum.EncodedColorPipelineData.coverBase free n ∧ ThreeSum.EncodedColorPipelineData.coverBase free n ≤ ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC ∧ ThreeSum.EncodedColorPipelineData.wantedHeader free n (List.length (ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC)) + OfNat.ofNat (nat_lit 4) ≤ ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC ∧ ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 3) ≤ ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC ∧ ThreeSum.EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 5) ≤ ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC) =>
                  And.casesOn right fun (left : free + OfNat.ofNat (nat_lit 8) ≤ ThreeSum.EncodedColorPipelineData.coverBase free n) (right : ThreeSum.EncodedColorPipelineData.coverBase free n ≤ ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC ∧ ThreeSum.EncodedColorPipelineData.wantedHeader free n (List.length (ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC)) + OfNat.ofNat (nat_lit 4) ≤ ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC ∧ ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 3) ≤ ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC ∧ ThreeSum.EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 5) ≤ ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC) =>
                    And.casesOn right fun (left : ThreeSum.EncodedColorPipelineData.coverBase free n ≤ ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC) (right : ThreeSum.EncodedColorPipelineData.wantedHeader free n (List.length (ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC)) + OfNat.ofNat (nat_lit 4) ≤ ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC ∧ ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 3) ≤ ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC ∧ ThreeSum.EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 5) ≤ ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC) =>
                      And.casesOn right fun (hwanted : ThreeSum.EncodedColorPipelineData.wantedHeader free n (List.length (ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC)) + OfNat.ofNat (nat_lit 4) ≤ ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC) (right : ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 3) ≤ ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC ∧ ThreeSum.EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 5) ≤ ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC) =>
                        And.casesOn right fun (hcontrols : ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 3) ≤ ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC) (hbank : ThreeSum.EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 5) ≤ ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC) =>
                          id
                            (fun (hwanted : wanted + OfNat.ofNat (nat_lit 4) ≤ controls) =>
                              id
                                (fun (hcontrols : controls + OfNat.ofNat (nat_lit 3) ≤ out) =>
                                  id
                                    (fun (hbank : bank + OfNat.ofNat (nat_lit 5) ≤ out) =>
                                      have hcover20 : cover + OfNat.ofNat (nat_lit 20) ≤ masks := ThreeSum.LightLocalCoverRetention.base_le_nextFree (ThreeSum.LightLocalCoverInit.base cover) h;
                                      have hmasks : ThreeSum.LightCoverKeys.afterCover cover h ≤ ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC := LE.le.trans (ThreeSum.LightCoverKeyData.afterCover_le_keyEnd cover h J) (ThreeSum.ThreeSumReportingSetupData.cover_end_le_report free n A B C hsA hsB hsC);
                                      id
                                        (fun (hmasks : masks ≤ report) =>
                                          have hpairs : pairs + OfNat.ofNat (nat_lit 2) * cnt = controls := rfl;
                                          And.casesOn (@ThreeSum.ThreeSumColorBudgets.normalized_lengths μ free n color x A B C hsA hsB hsC (@ThreeSum.ThreeSumReportingSetupData.Stored.encoded μ free n color x A B C hsA hsB hsC H)) fun (hnA : List.length A ≤ n) (right : List.length B ≤ n ∧ List.length C ≤ n) =>
                                            And.casesOn right fun (hnB : List.length B ≤ n) (hnC : List.length C ≤ n) =>
                                              have hR : List.length (ThreeSum.BandRawA.sortedRecords A B C g (ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC) ≤ ThreeSum.ColorBandBounds.count n g := @ThreeSum.EncodedColorNormalizedData.records_length_le A B C g n (ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC hnA hnB hnC;
                                              id
                                                (fun (hR : R ≤ ThreeSum.ColorBandBounds.count n g) =>
                                                  have hN : N ≤ g * ThreeSum.ColorBandBounds.count n g := id (id (Eq.mpr (id (congrArg (fun (_a : ℕ) => _a ≤ g * ThreeSum.ColorBandBounds.count n g) (ThreeSum.BandRawA.values_length (fun (j : ℕ) => List.getD A j (OfNat.ofNat (nat_lit 0))) (ThreeSum.BandRawA.items (List.length A) (ThreeSum.BandScales.bandSize n) (ThreeSum.BandRawA.sortedRecords A B C (ThreeSum.BandScales.bandSize n) (ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC))))) (LE.le.trans (ThreeSum.BandRawA.items_length_le (List.length A) (ThreeSum.BandScales.bandSize n) (ThreeSum.BandRawA.sortedRecords A B C (ThreeSum.BandScales.bandSize n) (ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC)) (Nat.mul_le_mul_left (ThreeSum.BandScales.bandSize n) hR))));
                                                  And.casesOn (ThreeSum.EncodedColorLayout.normalized_ends_cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n)) fun (left : ThreeSum.EncodedColorLayout.av free n + n ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n)) (right : ThreeSum.EncodedColorLayout.ae free n + OfNat.ofNat (nat_lit 2) + OfNat.ofNat (nat_lit 2) * n ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.EncodedColorLayout.bv free n + n ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.EncodedColorLayout.be free n + OfNat.ofNat (nat_lit 2) + OfNat.ofNat (nat_lit 2) * n ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.EncodedColorLayout.cv free n + n ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.EncodedColorLayout.ce free n + OfNat.ofNat (nat_lit 2) + OfNat.ofNat (nat_lit 2) * n ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.EncodedColorLayout.tables free n + ThreeSum.ColorBandBounds.count n g ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.EncodedColorLayout.rec free n g + OfNat.ofNat (nat_lit 4) * ThreeSum.ColorBandBounds.count n g ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.LightBandRawA.space (ThreeSum.EncodedColorLayout.vals free n g) (ThreeSum.ColorBandBounds.count n g) g ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n)) =>
                                                    And.casesOn right fun (hae : ThreeSum.EncodedColorLayout.ae free n + OfNat.ofNat (nat_lit 2) + OfNat.ofNat (nat_lit 2) * n ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n)) (right : ThreeSum.EncodedColorLayout.bv free n + n ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.EncodedColorLayout.be free n + OfNat.ofNat (nat_lit 2) + OfNat.ofNat (nat_lit 2) * n ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.EncodedColorLayout.cv free n + n ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.EncodedColorLayout.ce free n + OfNat.ofNat (nat_lit 2) + OfNat.ofNat (nat_lit 2) * n ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.EncodedColorLayout.tables free n + ThreeSum.ColorBandBounds.count n g ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.EncodedColorLayout.rec free n g + OfNat.ofNat (nat_lit 4) * ThreeSum.ColorBandBounds.count n g ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.LightBandRawA.space (ThreeSum.EncodedColorLayout.vals free n g) (ThreeSum.ColorBandBounds.count n g) g ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n)) =>
                                                      And.casesOn right fun (hbv : ThreeSum.EncodedColorLayout.bv free n + n ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n)) (right : ThreeSum.EncodedColorLayout.be free n + OfNat.ofNat (nat_lit 2) + OfNat.ofNat (nat_lit 2) * n ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.EncodedColorLayout.cv free n + n ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.EncodedColorLayout.ce free n + OfNat.ofNat (nat_lit 2) + OfNat.ofNat (nat_lit 2) * n ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.EncodedColorLayout.tables free n + ThreeSum.ColorBandBounds.count n g ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.EncodedColorLayout.rec free n g + OfNat.ofNat (nat_lit 4) * ThreeSum.ColorBandBounds.count n g ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.LightBandRawA.space (ThreeSum.EncodedColorLayout.vals free n g) (ThreeSum.ColorBandBounds.count n g) g ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n)) =>
                                                        And.casesOn right fun (hbe : ThreeSum.EncodedColorLayout.be free n + OfNat.ofNat (nat_lit 2) + OfNat.ofNat (nat_lit 2) * n ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n)) (right : ThreeSum.EncodedColorLayout.cv free n + n ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.EncodedColorLayout.ce free n + OfNat.ofNat (nat_lit 2) + OfNat.ofNat (nat_lit 2) * n ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.EncodedColorLayout.tables free n + ThreeSum.ColorBandBounds.count n g ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.EncodedColorLayout.rec free n g + OfNat.ofNat (nat_lit 4) * ThreeSum.ColorBandBounds.count n g ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.LightBandRawA.space (ThreeSum.EncodedColorLayout.vals free n g) (ThreeSum.ColorBandBounds.count n g) g ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n)) =>
                                                          And.casesOn right fun (hcv : ThreeSum.EncodedColorLayout.cv free n + n ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n)) (right : ThreeSum.EncodedColorLayout.ce free n + OfNat.ofNat (nat_lit 2) + OfNat.ofNat (nat_lit 2) * n ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.EncodedColorLayout.tables free n + ThreeSum.ColorBandBounds.count n g ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.EncodedColorLayout.rec free n g + OfNat.ofNat (nat_lit 4) * ThreeSum.ColorBandBounds.count n g ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.LightBandRawA.space (ThreeSum.EncodedColorLayout.vals free n g) (ThreeSum.ColorBandBounds.count n g) g ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n)) =>
                                                            And.casesOn right fun (hce : ThreeSum.EncodedColorLayout.ce free n + OfNat.ofNat (nat_lit 2) + OfNat.ofNat (nat_lit 2) * n ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n)) (right : ThreeSum.EncodedColorLayout.tables free n + ThreeSum.ColorBandBounds.count n g ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.EncodedColorLayout.rec free n g + OfNat.ofNat (nat_lit 4) * ThreeSum.ColorBandBounds.count n g ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.LightBandRawA.space (ThreeSum.EncodedColorLayout.vals free n g) (ThreeSum.ColorBandBounds.count n g) g ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n)) =>
                                                              And.casesOn right fun (left : ThreeSum.EncodedColorLayout.tables free n + ThreeSum.ColorBandBounds.count n g ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n)) (right : ThreeSum.EncodedColorLayout.rec free n g + OfNat.ofNat (nat_lit 4) * ThreeSum.ColorBandBounds.count n g ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) ∧ ThreeSum.LightBandRawA.space (ThreeSum.EncodedColorLayout.vals free n g) (ThreeSum.ColorBandBounds.count n g) g ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n)) =>
                                                                And.casesOn right fun (hrec : ThreeSum.EncodedColorLayout.rec free n g + OfNat.ofNat (nat_lit 4) * ThreeSum.ColorBandBounds.count n g ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n)) (hvals : ThreeSum.LightBandRawA.space (ThreeSum.EncodedColorLayout.vals free n g) (ThreeSum.ColorBandBounds.count n g) g ≤ ThreeSum.EncodedColorLayout.cover free n g (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n)) =>
                                                                  id
                                                                    (fun (hae : ae + OfNat.ofNat (nat_lit 2) + OfNat.ofNat (nat_lit 2) * n ≤ cover) =>
                                                                      id
                                                                        (fun (hbv : bv + n ≤ cover) =>
                                                                          id
                                                                            (fun (hbe : be + OfNat.ofNat (nat_lit 2) + OfNat.ofNat (nat_lit 2) * n ≤ cover) =>
                                                                              id
                                                                                (fun (hcv : cv + n ≤ cover) =>
                                                                                  id
                                                                                    (fun (hce : ce + OfNat.ofNat (nat_lit 2) + OfNat.ofNat (nat_lit 2) * n ≤ cover) =>
                                                                                      id
                                                                                        (fun (hrec : recs + OfNat.ofNat (nat_lit 4) * ThreeSum.ColorBandBounds.count n g ≤ cover) =>
                                                                                          id
                                                                                            (fun (hvals : ThreeSum.LightBandRawA.space vals (ThreeSum.ColorBandBounds.count n g) g ≤ cover) =>
                                                                                              have howner : owners ≤ cover :=
                                                                                                have hh : g * R ≤ g * ThreeSum.ColorBandBounds.count n g := Nat.mul_le_mul_left g hR;
                                                                                                id (id (id (Decidable.byContradiction fun (a : ¬vals + g * R ≤ cover) => @ThreeSum.LightThreeSumWantedHost.program_meets._proof_1_1 lim d free n params A B C hsA hsB hsC hvals hh a)));
                                                                                              have hval : vals ≤ cover := Decidable.byContradiction fun (a : ¬vals ≤ cover) => @ThreeSum.LightThreeSumWantedHost.program_meets._proof_1_2 lim d free n params A B C hsA hsB hsC howner a;
                                                                                              have hbound : ∀ (z : ℕ) (hz : z ≤ ThreeSum.LightThreeSumWantedHost.word n), Nat.cast z ≤ Light.Limits.word lim := fun (z : ℕ) (hz : z ≤ ThreeSum.LightThreeSumWantedHost.word n) => LE.le.trans (Iff.mpr Int.ofNat_le hz) hword;
                                                                                              And.casesOn (ThreeSum.LightThreeSumWantedHost.word_bounds n) fun (wn : n ≤ ThreeSum.LightThreeSumWantedHost.word n) (right : ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.LightSwitchDepth.depth (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)) + OfNat.ofNat (nat_lit 1) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.BandScales.bandSize n ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.Scales.radix n ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.OutputDecodeRecords.layerCount (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n)) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.GlobalEncoding.scheduleSize (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n)) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.BandScales.bandSize n * ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n) ≤ ThreeSum.LightThreeSumWantedHost.word n) =>
                                                                                                And.casesOn right fun (wJ : ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n) ≤ ThreeSum.LightThreeSumWantedHost.word n) (right : ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.LightSwitchDepth.depth (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)) + OfNat.ofNat (nat_lit 1) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.BandScales.bandSize n ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.Scales.radix n ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.OutputDecodeRecords.layerCount (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n)) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.GlobalEncoding.scheduleSize (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n)) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.BandScales.bandSize n * ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n) ≤ ThreeSum.LightThreeSumWantedHost.word n) =>
                                                                                                  And.casesOn right fun (wh : ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n) ≤ ThreeSum.LightThreeSumWantedHost.word n) (right : ThreeSum.LightSwitchDepth.depth (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)) + OfNat.ofNat (nat_lit 1) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.BandScales.bandSize n ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.Scales.radix n ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.OutputDecodeRecords.layerCount (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n)) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.GlobalEncoding.scheduleSize (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n)) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.BandScales.bandSize n * ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n) ≤ ThreeSum.LightThreeSumWantedHost.word n) =>
                                                                                                    And.casesOn right fun (wK : ThreeSum.LightSwitchDepth.depth (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)) + OfNat.ofNat (nat_lit 1) ≤ ThreeSum.LightThreeSumWantedHost.word n) (right : ThreeSum.BandScales.bandSize n ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.Scales.radix n ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.OutputDecodeRecords.layerCount (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n)) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.GlobalEncoding.scheduleSize (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n)) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.BandScales.bandSize n * ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n) ≤ ThreeSum.LightThreeSumWantedHost.word n) =>
                                                                                                      And.casesOn right fun (wg : ThreeSum.BandScales.bandSize n ≤ ThreeSum.LightThreeSumWantedHost.word n) (right : ThreeSum.Scales.radix n ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.OutputDecodeRecords.layerCount (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n)) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.GlobalEncoding.scheduleSize (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n)) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.BandScales.bandSize n * ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n) ≤ ThreeSum.LightThreeSumWantedHost.word n) =>
                                                                                                        And.casesOn right fun (wM : ThreeSum.Scales.radix n ≤ ThreeSum.LightThreeSumWantedHost.word n) (right : ThreeSum.OutputDecodeRecords.layerCount (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n)) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.GlobalEncoding.scheduleSize (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n)) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.BandScales.bandSize n * ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n) ≤ ThreeSum.LightThreeSumWantedHost.word n) =>
                                                                                                          And.casesOn right fun (wl : ThreeSum.OutputDecodeRecords.layerCount (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n)) ≤ ThreeSum.LightThreeSumWantedHost.word n) (right : ThreeSum.GlobalEncoding.scheduleSize (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n)) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.BandScales.bandSize n * ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n) ≤ ThreeSum.LightThreeSumWantedHost.word n) =>
                                                                                                            And.casesOn right fun (ws : ThreeSum.GlobalEncoding.scheduleSize (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n)) ≤ ThreeSum.LightThreeSumWantedHost.word n) (right : ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n) ≤ ThreeSum.LightThreeSumWantedHost.word n ∧ ThreeSum.BandScales.bandSize n * ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n) ≤ ThreeSum.LightThreeSumWantedHost.word n) =>
                                                                                                              And.casesOn right fun (wR : ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n) ≤ ThreeSum.LightThreeSumWantedHost.word n) (wN : ThreeSum.BandScales.bandSize n * ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n) ≤ ThreeSum.LightThreeSumWantedHost.word n) =>
                                                                                                                have hnword : Nat.cast n ≤ Light.Limits.word lim := hbound n wn;
                                                                                                                have hJword : Nat.cast J ≤ Light.Limits.word lim := hbound J wJ;
                                                                                                                have hhword : Nat.cast h ≤ Light.Limits.word lim := hbound h wh;
                                                                                                                have hKword : Nat.cast (K + OfNat.ofNat (nat_lit 1)) ≤ Light.Limits.word lim := hbound (K + OfNat.ofNat (nat_lit 1)) wK;
                                                                                                                have hgword : Nat.cast g ≤ Light.Limits.word lim := hbound g wg;
                                                                                                                have hMword : Nat.cast (ThreeSum.Scales.radix n) ≤ Light.Limits.word lim := hbound (ThreeSum.Scales.radix n) wM;
                                                                                                                have hlword : Nat.cast layers ≤ Light.Limits.word lim := hbound layers wl;
                                                                                                                have hsword : Nat.cast schedule ≤ Light.Limits.word lim := hbound schedule ws;
                                                                                                                have hRword : Nat.cast R ≤ Light.Limits.word lim := hbound R (LE.le.trans hR wR);
                                                                                                                have hNword : Nat.cast N ≤ Light.Limits.word lim := hbound N (LE.le.trans hN wN);
                                                                                                                have hGA : ThreeSum.BandPartition.size (List.length A) g ≤ List.length A := ThreeSum.BandPartition.size_le (List.length A) g;
                                                                                                                have hGB : ThreeSum.BandPartition.size (List.length B) g ≤ List.length B := ThreeSum.BandPartition.size_le (List.length B) g;
                                                                                                                have hGC : ThreeSum.BandPartition.size (List.length C) g ≤ List.length C := ThreeSum.BandPartition.size_le (List.length C) g;
                                                                                                                have hReq : R = ThreeSum.BandPartition.size (List.length B) g * ThreeSum.BandPartition.size (List.length C) g + ThreeSum.BandPartition.size (List.length A) g * ThreeSum.BandPartition.size (List.length B) g + ThreeSum.BandPartition.size (List.length A) g * ThreeSum.BandPartition.size (List.length C) g := ThreeSum.ThreeSumWantedHostData.recordCount_eq n A B C hsA hsB hsC;
                                                                                                                have hRsum : Nat.cast (ThreeSum.BandPartition.size (List.length B) g) * Nat.cast (ThreeSum.BandPartition.size (List.length C) g) + Nat.cast (ThreeSum.BandPartition.size (List.length A) g) * Nat.cast (ThreeSum.BandPartition.size (List.length B) g) + Nat.cast (ThreeSum.BandPartition.size (List.length A) g) * Nat.cast (ThreeSum.BandPartition.size (List.length C) g) ≤ Light.Limits.word lim := Eq.mp (congrFun' (congrArg LE.le (Eq.trans (Eq.trans (congrArg Nat.cast hReq) (Nat.cast_add (ThreeSum.BandPartition.size (List.length B) g * ThreeSum.BandPartition.size (List.length C) g + ThreeSum.BandPartition.size (List.length A) g * ThreeSum.BandPartition.size (List.length B) g) (ThreeSum.BandPartition.size (List.length A) g * ThreeSum.BandPartition.size (List.length C) g))) (congr (congrArg HAdd.hAdd (Eq.trans (Nat.cast_add (ThreeSum.BandPartition.size (List.length B) g * ThreeSum.BandPartition.size (List.length C) g) (ThreeSum.BandPartition.size (List.length A) g * ThreeSum.BandPartition.size (List.length B) g)) (congr (congrArg HAdd.hAdd (Nat.cast_mul (ThreeSum.BandPartition.size (List.length B) g) (ThreeSum.BandPartition.size (List.length C) g))) (Nat.cast_mul (ThreeSum.BandPartition.size (List.length A) g) (ThreeSum.BandPartition.size (List.length B) g))))) (Nat.cast_mul (ThreeSum.BandPartition.size (List.length A) g) (ThreeSum.BandPartition.size (List.length C) g))))) (Light.Limits.word lim)) hRword;
                                                                                                                have hBC0 : OfNat.ofNat (nat_lit 0) ≤ Nat.cast (ThreeSum.BandPartition.size (List.length B) g) * Nat.cast (ThreeSum.BandPartition.size (List.length C) g) := mul_nonneg (Nat.cast_nonneg' (ThreeSum.BandPartition.size (List.length B) g)) (Nat.cast_nonneg' (ThreeSum.BandPartition.size (List.length C) g));
                                                                                                                have hAB0 : OfNat.ofNat (nat_lit 0) ≤ Nat.cast (ThreeSum.BandPartition.size (List.length A) g) * Nat.cast (ThreeSum.BandPartition.size (List.length B) g) := mul_nonneg (Nat.cast_nonneg' (ThreeSum.BandPartition.size (List.length A) g)) (Nat.cast_nonneg' (ThreeSum.BandPartition.size (List.length B) g));
                                                                                                                have hAC0 : OfNat.ofNat (nat_lit 0) ≤ Nat.cast (ThreeSum.BandPartition.size (List.length A) g) * Nat.cast (ThreeSum.BandPartition.size (List.length C) g) := mul_nonneg (Nat.cast_nonneg' (ThreeSum.BandPartition.size (List.length A) g)) (Nat.cast_nonneg' (ThreeSum.BandPartition.size (List.length C) g));
                                                                                                                have hownerZ : Nat.cast vals + Nat.cast g * Nat.cast R = Nat.cast owners := of_eq_true (Eq.trans (congrArg (Eq (Nat.cast vals + Nat.cast g * Nat.cast R)) (Eq.trans (Eq.trans (congrArg Nat.cast (ThreeSum.LightBandRawA.ownerBase.eq_1 vals R g)) (Nat.cast_add vals (g * R))) (congrArg (HAdd.hAdd (Nat.cast vals)) (Nat.cast_mul g R)))) (eq_self (Nat.cast vals + Nat.cast g * Nat.cast R)));
                                                                                                                And.casesOn (@ThreeSum.EncodedColorPipelineData.Stored.heads_read μ free n color x A B C hsA hsB hsC (@ThreeSum.ThreeSumReportingSetupData.Stored.encoded μ free n color x A B C hsA hsB hsC H)) fun (left : μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC) = Nat.cast (ThreeSum.EncodedColorLayout.prime free n (ThreeSum.BandScales.bandSize n))) (right : μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 1)) = Nat.cast (ThreeSum.EncodedColorPipelineData.coverBase free n) ∧ μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 2)) = Nat.cast (ThreeSum.EncodedColorPipelineData.wantedHeader free n (List.length (ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC))) ∧ μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 3)) = Nat.cast (ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC) ∧ μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 4)) = Nat.cast (ThreeSum.EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC) ∧ μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 5)) = Nat.cast (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 8)) ∧ μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 6)) = Nat.cast (List.length (ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC)) ∧ μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 7)) = Nat.cast (ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)) =>
                                                                                                                  And.casesOn right fun (readCover : μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 1)) = Nat.cast (ThreeSum.EncodedColorPipelineData.coverBase free n)) (right : μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 2)) = Nat.cast (ThreeSum.EncodedColorPipelineData.wantedHeader free n (List.length (ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC))) ∧ μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 3)) = Nat.cast (ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC) ∧ μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 4)) = Nat.cast (ThreeSum.EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC) ∧ μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 5)) = Nat.cast (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 8)) ∧ μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 6)) = Nat.cast (List.length (ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC)) ∧ μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 7)) = Nat.cast (ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)) =>
                                                                                                                    And.casesOn right fun (readWanted : μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 2)) = Nat.cast (ThreeSum.EncodedColorPipelineData.wantedHeader free n (List.length (ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC)))) (right : μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 3)) = Nat.cast (ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC) ∧ μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 4)) = Nat.cast (ThreeSum.EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC) ∧ μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 5)) = Nat.cast (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 8)) ∧ μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 6)) = Nat.cast (List.length (ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC)) ∧ μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 7)) = Nat.cast (ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)) =>
                                                                                                                      And.casesOn right fun (readControls : μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 3)) = Nat.cast (ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC)) (right : μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 4)) = Nat.cast (ThreeSum.EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC) ∧ μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 5)) = Nat.cast (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 8)) ∧ μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 6)) = Nat.cast (List.length (ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC)) ∧ μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 7)) = Nat.cast (ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)) =>
                                                                                                                        And.casesOn right fun (readBank : μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 4)) = Nat.cast (ThreeSum.EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC)) (right : μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 5)) = Nat.cast (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 8)) ∧ μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 6)) = Nat.cast (List.length (ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC)) ∧ μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 7)) = Nat.cast (ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)) =>
                                                                                                                          And.casesOn right fun (left : μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 5)) = Nat.cast (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 8))) (right : μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 6)) = Nat.cast (List.length (ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC)) ∧ μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 7)) = Nat.cast (ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)) =>
                                                                                                                            And.casesOn right fun (readN : μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 6)) = Nat.cast (List.length (ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC))) (right : μ (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC + OfNat.ofNat (nat_lit 7)) = Nat.cast (ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)) =>
                                                                                                                              id
                                                                                                                                (fun (readCover : μ (out + OfNat.ofNat (nat_lit 1)) = Nat.cast cover) =>
                                                                                                                                  id
                                                                                                                                    (fun (readWanted : μ (out + OfNat.ofNat (nat_lit 2)) = Nat.cast wanted) =>
                                                                                                                                      id
                                                                                                                                        (fun (readControls : μ (out + OfNat.ofNat (nat_lit 3)) = Nat.cast controls) =>
                                                                                                                                          id
                                                                                                                                            (fun (readBank : μ (out + OfNat.ofNat (nat_lit 4)) = Nat.cast bank) =>
                                                                                                                                              id
                                                                                                                                                (fun (readN : μ (out + OfNat.ofNat (nat_lit 6)) = Nat.cast N) =>
                                                                                                                                                  And.casesOn (@ThreeSum.EncodedColorNormalizedData.heads_read μ free n (ThreeSum.BandScales.bandSize n) (@ThreeSum.EncodedColorPipelineData.Stored.normalizedHeads μ free n color x A B C hsA hsB hsC (@ThreeSum.ThreeSumReportingSetupData.Stored.encoded μ free n color x A B C hsA hsB hsC H))) fun (left : μ free = Nat.cast (ThreeSum.EncodedColorLayout.av free n)) (right : μ (free + OfNat.ofNat (nat_lit 1)) = Nat.cast (ThreeSum.EncodedColorLayout.ae free n) ∧ μ (free + OfNat.ofNat (nat_lit 2)) = Nat.cast (ThreeSum.EncodedColorLayout.bv free n) ∧ μ (free + OfNat.ofNat (nat_lit 3)) = Nat.cast (ThreeSum.EncodedColorLayout.be free n) ∧ μ (free + OfNat.ofNat (nat_lit 4)) = Nat.cast (ThreeSum.EncodedColorLayout.cv free n) ∧ μ (free + OfNat.ofNat (nat_lit 5)) = Nat.cast (ThreeSum.EncodedColorLayout.ce free n) ∧ μ (free + OfNat.ofNat (nat_lit 6)) = Nat.cast (ThreeSum.EncodedColorLayout.rec free n (ThreeSum.BandScales.bandSize n)) ∧ μ (free + OfNat.ofNat (nat_lit 7)) = Nat.cast (ThreeSum.EncodedColorLayout.vals free n (ThreeSum.BandScales.bandSize n))) =>
                                                                                                                                                    And.casesOn right fun (readAE : μ (free + OfNat.ofNat (nat_lit 1)) = Nat.cast (ThreeSum.EncodedColorLayout.ae free n)) (right : μ (free + OfNat.ofNat (nat_lit 2)) = Nat.cast (ThreeSum.EncodedColorLayout.bv free n) ∧ μ (free + OfNat.ofNat (nat_lit 3)) = Nat.cast (ThreeSum.EncodedColorLayout.be free n) ∧ μ (free + OfNat.ofNat (nat_lit 4)) = Nat.cast (ThreeSum.EncodedColorLayout.cv free n) ∧ μ (free + OfNat.ofNat (nat_lit 5)) = Nat.cast (ThreeSum.EncodedColorLayout.ce free n) ∧ μ (free + OfNat.ofNat (nat_lit 6)) = Nat.cast (ThreeSum.EncodedColorLayout.rec free n (ThreeSum.BandScales.bandSize n)) ∧ μ (free + OfNat.ofNat (nat_lit 7)) = Nat.cast (ThreeSum.EncodedColorLayout.vals free n (ThreeSum.BandScales.bandSize n))) =>
                                                                                                                                                      And.casesOn right fun (readB : μ (free + OfNat.ofNat (nat_lit 2)) = Nat.cast (ThreeSum.EncodedColorLayout.bv free n)) (right : μ (free + OfNat.ofNat (nat_lit 3)) = Nat.cast (ThreeSum.EncodedColorLayout.be free n) ∧ μ (free + OfNat.ofNat (nat_lit 4)) = Nat.cast (ThreeSum.EncodedColorLayout.cv free n) ∧ μ (free + OfNat.ofNat (nat_lit 5)) = Nat.cast (ThreeSum.EncodedColorLayout.ce free n) ∧ μ (free + OfNat.ofNat (nat_lit 6)) = Nat.cast (ThreeSum.EncodedColorLayout.rec free n (ThreeSum.BandScales.bandSize n)) ∧ μ (free + OfNat.ofNat (nat_lit 7)) = Nat.cast (ThreeSum.EncodedColorLayout.vals free n (ThreeSum.BandScales.bandSize n))) =>
                                                                                                                                                        And.casesOn right fun (readBE : μ (free + OfNat.ofNat (nat_lit 3)) = Nat.cast (ThreeSum.EncodedColorLayout.be free n)) (right : μ (free + OfNat.ofNat (nat_lit 4)) = Nat.cast (ThreeSum.EncodedColorLayout.cv free n) ∧ μ (free + OfNat.ofNat (nat_lit 5)) = Nat.cast (ThreeSum.EncodedColorLayout.ce free n) ∧ μ (free + OfNat.ofNat (nat_lit 6)) = Nat.cast (ThreeSum.EncodedColorLayout.rec free n (ThreeSum.BandScales.bandSize n)) ∧ μ (free + OfNat.ofNat (nat_lit 7)) = Nat.cast (ThreeSum.EncodedColorLayout.vals free n (ThreeSum.BandScales.bandSize n))) =>
                                                                                                                                                          And.casesOn right fun (readC : μ (free + OfNat.ofNat (nat_lit 4)) = Nat.cast (ThreeSum.EncodedColorLayout.cv free n)) (right : μ (free + OfNat.ofNat (nat_lit 5)) = Nat.cast (ThreeSum.EncodedColorLayout.ce free n) ∧ μ (free + OfNat.ofNat (nat_lit 6)) = Nat.cast (ThreeSum.EncodedColorLayout.rec free n (ThreeSum.BandScales.bandSize n)) ∧ μ (free + OfNat.ofNat (nat_lit 7)) = Nat.cast (ThreeSum.EncodedColorLayout.vals free n (ThreeSum.BandScales.bandSize n))) =>
                                                                                                                                                            And.casesOn right fun (readCE : μ (free + OfNat.ofNat (nat_lit 5)) = Nat.cast (ThreeSum.EncodedColorLayout.ce free n)) (right : μ (free + OfNat.ofNat (nat_lit 6)) = Nat.cast (ThreeSum.EncodedColorLayout.rec free n (ThreeSum.BandScales.bandSize n)) ∧ μ (free + OfNat.ofNat (nat_lit 7)) = Nat.cast (ThreeSum.EncodedColorLayout.vals free n (ThreeSum.BandScales.bandSize n))) =>
                                                                                                                                                              And.casesOn right fun (readRecs : μ (free + OfNat.ofNat (nat_lit 6)) = Nat.cast (ThreeSum.EncodedColorLayout.rec free n (ThreeSum.BandScales.bandSize n))) (readVals : μ (free + OfNat.ofNat (nat_lit 7)) = Nat.cast (ThreeSum.EncodedColorLayout.vals free n (ThreeSum.BandScales.bandSize n))) =>
                                                                                                                                                                id
                                                                                                                                                                  (fun (readAE : μ (free + OfNat.ofNat (nat_lit 1)) = Nat.cast ae) =>
                                                                                                                                                                    id
                                                                                                                                                                      (fun (readB : μ (free + OfNat.ofNat (nat_lit 2)) = Nat.cast bv) =>
                                                                                                                                                                        id
                                                                                                                                                                          (fun (readBE : μ (free + OfNat.ofNat (nat_lit 3)) = Nat.cast be) =>
                                                                                                                                                                            id
                                                                                                                                                                              (fun (readC : μ (free + OfNat.ofNat (nat_lit 4)) = Nat.cast cv) =>
                                                                                                                                                                                id
                                                                                                                                                                                  (fun (readCE : μ (free + OfNat.ofNat (nat_lit 5)) = Nat.cast ce) =>
                                                                                                                                                                                    id
                                                                                                                                                                                      (fun (readRecs : μ (free + OfNat.ofNat (nat_lit 6)) = Nat.cast recs) =>
                                                                                                                                                                                        id
                                                                                                                                                                                          (fun (readVals : μ (free + OfNat.ofNat (nat_lit 7)) = Nat.cast vals) =>
                                                                                                                                                                                            And.casesOn (@ThreeSum.EncodedColorParameterData.reads μ params n Hparams) fun (left : μ params = Nat.cast (ThreeSum.Scales.inputBits n)) (right : μ (params + OfNat.ofNat (nat_lit 1)) = Nat.cast (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n)) ∧ μ (params + OfNat.ofNat (nat_lit 3)) = Nat.cast (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)) ∧ μ (params + OfNat.ofNat (nat_lit 4)) = Nat.cast (ThreeSum.Scales.mu n) ∧ μ (params + OfNat.ofNat (nat_lit 14)) = Nat.cast (ThreeSum.Scales.radix n) ∧ μ (params + OfNat.ofNat (nat_lit 17)) = Nat.cast (ThreeSum.BandScales.bandSize n) ∧ μ (params + OfNat.ofNat (nat_lit 18)) = Nat.cast (ThreeSum.Scales.primeWindow n)) =>
                                                                                                                                                                                              And.casesOn right fun (readH : μ (params + OfNat.ofNat (nat_lit 1)) = Nat.cast (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))) (right : μ (params + OfNat.ofNat (nat_lit 3)) = Nat.cast (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)) ∧ μ (params + OfNat.ofNat (nat_lit 4)) = Nat.cast (ThreeSum.Scales.mu n) ∧ μ (params + OfNat.ofNat (nat_lit 14)) = Nat.cast (ThreeSum.Scales.radix n) ∧ μ (params + OfNat.ofNat (nat_lit 17)) = Nat.cast (ThreeSum.BandScales.bandSize n) ∧ μ (params + OfNat.ofNat (nat_lit 18)) = Nat.cast (ThreeSum.Scales.primeWindow n)) =>
                                                                                                                                                                                                And.casesOn right fun (readJ : μ (params + OfNat.ofNat (nat_lit 3)) = Nat.cast (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n))) (right : μ (params + OfNat.ofNat (nat_lit 4)) = Nat.cast (ThreeSum.Scales.mu n) ∧ μ (params + OfNat.ofNat (nat_lit 14)) = Nat.cast (ThreeSum.Scales.radix n) ∧ μ (params + OfNat.ofNat (nat_lit 17)) = Nat.cast (ThreeSum.BandScales.bandSize n) ∧ μ (params + OfNat.ofNat (nat_lit 18)) = Nat.cast (ThreeSum.Scales.primeWindow n)) =>
                                                                                                                                                                                                  And.casesOn right fun (left : μ (params + OfNat.ofNat (nat_lit 4)) = Nat.cast (ThreeSum.Scales.mu n)) (right : μ (params + OfNat.ofNat (nat_lit 14)) = Nat.cast (ThreeSum.Scales.radix n) ∧ μ (params + OfNat.ofNat (nat_lit 17)) = Nat.cast (ThreeSum.BandScales.bandSize n) ∧ μ (params + OfNat.ofNat (nat_lit 18)) = Nat.cast (ThreeSum.Scales.primeWindow n)) =>
                                                                                                                                                                                                    And.casesOn right fun (readM : μ (params + OfNat.ofNat (nat_lit 14)) = Nat.cast (ThreeSum.Scales.radix n)) (right : μ (params + OfNat.ofNat (nat_lit 17)) = Nat.cast (ThreeSum.BandScales.bandSize n) ∧ μ (params + OfNat.ofNat (nat_lit 18)) = Nat.cast (ThreeSum.Scales.primeWindow n)) =>
                                                                                                                                                                                                      And.casesOn right fun (readG : μ (params + OfNat.ofNat (nat_lit 17)) = Nat.cast (ThreeSum.BandScales.bandSize n)) (right : μ (params + OfNat.ofNat (nat_lit 18)) = Nat.cast (ThreeSum.Scales.primeWindow n)) =>
                                                                                                                                                                                                        id
                                                                                                                                                                                                          (fun (readH : μ (params + OfNat.ofNat (nat_lit 1)) = Nat.cast h) =>
                                                                                                                                                                                                            id
                                                                                                                                                                                                              (fun (readJ : μ (params + OfNat.ofNat (nat_lit 3)) = Nat.cast J) =>
                                                                                                                                                                                                                id
                                                                                                                                                                                                                  (fun (readG : μ (params + OfNat.ofNat (nat_lit 17)) = Nat.cast g) =>
                                                                                                                                                                                                                    And.casesOn (@ThreeSum.SourceFiniteInputs.prepared_headers μ (ThreeSum.EncodedColorLayout.av free n) (ThreeSum.EncodedColorLayout.ae free n) (ThreeSum.BandScales.bandSize n) (ThreeSum.BandScales.bandSize_pos n) (@ThreeSum.ColorClassLists.classList n (ThreeSum.Scales.inputBits n + OfNat.ofNat (nat_lit 1)) color x (OfNat.ofNat (nat_lit 0)) (OfNat.ofNat (nat_lit 1))) A hsA (And.left (And.right (@ThreeSum.EncodedColorPipelineData.Stored.normalized μ free n color x A B C hsA hsB hsC (@ThreeSum.ThreeSumReportingSetupData.Stored.encoded μ free n color x A B C hsA hsB hsC H))))) fun (left : μ (ThreeSum.EncodedColorLayout.ae free n) = Nat.cast (List.length A)) (readGA : μ (ThreeSum.EncodedColorLayout.ae free n + OfNat.ofNat (nat_lit 1)) = Nat.cast (ThreeSum.BandPartition.size (List.length A) (ThreeSum.BandScales.bandSize n))) =>
                                                                                                                                                                                                                      And.casesOn (@ThreeSum.SourceFiniteInputs.prepared_headers μ (ThreeSum.EncodedColorLayout.bv free n) (ThreeSum.EncodedColorLayout.be free n) (ThreeSum.BandScales.bandSize n) (ThreeSum.BandScales.bandSize_pos n) (@ThreeSum.ColorClassLists.classList n (ThreeSum.Scales.inputBits n + OfNat.ofNat (nat_lit 1)) color x (OfNat.ofNat (nat_lit 1)) (OfNat.ofNat (nat_lit 1))) B hsB (And.left (And.right (And.right (@ThreeSum.EncodedColorPipelineData.Stored.normalized μ free n color x A B C hsA hsB hsC (@ThreeSum.ThreeSumReportingSetupData.Stored.encoded μ free n color x A B C hsA hsB hsC H)))))) fun (readNB : μ (ThreeSum.EncodedColorLayout.be free n) = Nat.cast (List.length B)) (readGB : μ (ThreeSum.EncodedColorLayout.be free n + OfNat.ofNat (nat_lit 1)) = Nat.cast (ThreeSum.BandPartition.size (List.length B) (ThreeSum.BandScales.bandSize n))) =>
                                                                                                                                                                                                                        And.casesOn (@ThreeSum.SourceFiniteInputs.prepared_headers μ (ThreeSum.EncodedColorLayout.cv free n) (ThreeSum.EncodedColorLayout.ce free n) (ThreeSum.BandScales.bandSize n) (ThreeSum.BandScales.bandSize_pos n) (@ThreeSum.ColorClassLists.classList n (ThreeSum.Scales.inputBits n + OfNat.ofNat (nat_lit 1)) color x (OfNat.ofNat (nat_lit 2)) (-OfNat.ofNat (nat_lit 1))) C hsC (And.left (And.right (And.right (And.right (@ThreeSum.EncodedColorPipelineData.Stored.normalized μ free n color x A B C hsA hsB hsC (@ThreeSum.ThreeSumReportingSetupData.Stored.encoded μ free n color x A B C hsA hsB hsC H))))))) fun (readNC : μ (ThreeSum.EncodedColorLayout.ce free n) = Nat.cast (List.length C)) (readGC : μ (ThreeSum.EncodedColorLayout.ce free n + OfNat.ofNat (nat_lit 1)) = Nat.cast (ThreeSum.BandPartition.size (List.length C) (ThreeSum.BandScales.bandSize n))) =>
                                                                                                                                                                                                                          id
                                                                                                                                                                                                                            (fun (readGA : μ (ae + OfNat.ofNat (nat_lit 1)) = Nat.cast (ThreeSum.BandPartition.size (List.length A) g)) =>
                                                                                                                                                                                                                              id
                                                                                                                                                                                                                                (fun (readGB : μ (be + OfNat.ofNat (nat_lit 1)) = Nat.cast (ThreeSum.BandPartition.size (List.length B) g)) =>
                                                                                                                                                                                                                                  id
                                                                                                                                                                                                                                    (fun (readGC : μ (ce + OfNat.ofNat (nat_lit 1)) = Nat.cast (ThreeSum.BandPartition.size (List.length C) g)) =>
                                                                                                                                                                                                                                      id
                                                                                                                                                                                                                                        (fun (readNB : μ be = Nat.cast (List.length B)) =>
                                                                                                                                                                                                                                          id
                                                                                                                                                                                                                                            (fun (readNC : μ ce = Nat.cast (List.length C)) =>
                                                                                                                                                                                                                                              have readCount : μ wanted = Nat.cast cnt := @ThreeSum.ThreeSumWantedHostData.count_read μ free n color x A B C hsA hsB hsC (@ThreeSum.ThreeSumReportingSetupData.Stored.encoded μ free n color x A B C hsA hsB hsC H);
                                                                                                                                                                                                                                              have readPairs : μ (wanted + OfNat.ofNat (nat_lit 1)) = Nat.cast pairs := @ThreeSum.ThreeSumWantedHostData.pairs_read μ free n color x A B C hsA hsB hsC (@ThreeSum.ThreeSumReportingSetupData.Stored.encoded μ free n color x A B C hsA hsB hsC H);
                                                                                                                                                                                                                                              have readLevels : μ (report + OfNat.ofNat (nat_lit 2)) = Nat.cast (K + OfNat.ofNat (nat_lit 1)) := @ThreeSum.LightThreeSumWantedHost.report_level_read μ report (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n)) J (List.length B) (List.length C) (ThreeSum.BandScales.bandSize n) (fun (j : ℕ) => List.getD B j (OfNat.ofNat (nat_lit 0))) (fun (j : ℕ) => List.getD C j (OfNat.ofNat (nat_lit 0))) (Nat.cast (ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)) (ThreeSum.ThreeSumReportingSetupData.shift n A B C hsA hsB hsC) (@ThreeSum.ThreeSumReportingSetupData.Stored.catalog μ free n color x A B C hsA hsB hsC H);
                                                                                                                                                                                                                                              And.casesOn (@ThreeSum.LightThreeSumWantedHost.cover_header_reads μ (ThreeSum.EncodedColorPipelineData.coverBase free n) (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n)) (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)) (@ThreeSum.EncodedColorPipelineData.Stored.cover μ free n color x A B C hsA hsB hsC (@ThreeSum.ThreeSumReportingSetupData.Stored.encoded μ free n color x A B C hsA hsB hsC H))) fun (readLayers : μ (ThreeSum.EncodedColorPipelineData.coverBase free n) = Nat.cast (ThreeSum.OutputDecodeRecords.layerCount (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n)))) (right : μ (ThreeSum.EncodedColorPipelineData.coverBase free n + OfNat.ofNat (nat_lit 10)) = Nat.cast (ThreeSum.GlobalEncoding.scheduleSize (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))) ∧ μ (ThreeSum.EncodedColorPipelineData.coverBase free n + OfNat.ofNat (nat_lit 18)) = Nat.cast (ThreeSum.LightCoverKeys.afterCover (ThreeSum.EncodedColorPipelineData.coverBase free n) (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n)))) => And.casesOn right fun (readSchedule : μ (ThreeSum.EncodedColorPipelineData.coverBase free n + OfNat.ofNat (nat_lit 10)) = Nat.cast (ThreeSum.GlobalEncoding.scheduleSize (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n)))) (readMasks : μ (ThreeSum.EncodedColorPipelineData.coverBase free n + OfNat.ofNat (nat_lit 18)) = Nat.cast (ThreeSum.LightCoverKeys.afterCover (ThreeSum.EncodedColorPipelineData.coverBase free n) (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n)))) => id (fun (readLayers : μ cover = Nat.cast layers) => id (fun (readSchedule : μ (cover + OfNat.ofNat (nat_lit 10)) = Nat.cast schedule) => id (fun (readMasks : μ (cover + OfNat.ofNat (nat_lit 18)) = Nat.cast masks) => id (fun (hscan : Light.Meets lim ThreeSum.LightReportingWantedScan.program (OfNat.ofNat (nat_lit 152)) (d + OfNat.ofNat (nat_lit 1)) [Nat.cast cnt, Nat.cast (ctr + OfNat.ofNat (nat_lit 4)), Nat.cast J, Nat.cast h, Nat.cast K, Nat.cast N, Nat.cast (List.length B), Nat.cast (List.length C), Nat.cast cover, Nat.cast ctr, Nat.cast pairs, Nat.cast layers, Nat.cast schedule, Nat.cast masks, Nat.cast vals, Nat.cast owners, Nat.cast recs, Nat.cast (controls + OfNat.ofNat (nat_lit 3)), Nat.cast bank, Nat.cast bv, Nat.cast cv, Nat.cast report, Nat.cast (ThreeSum.Scales.radix n)] μ T Q) => @ThreeSum.LightThreeSumWantedHost.header_meets lim d T μ n params free (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC) (ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC) report cover controls bank ae bv be cv ce vals recs h J K g R N wanted cnt pairs layers schedule masks owners (ThreeSum.Scales.radix n) (List.length B) (List.length C) (ThreeSum.BandPartition.size (List.length A) g) (ThreeSum.BandPartition.size (List.length B) g) (ThreeSum.BandPartition.size (List.length C) g) Q hparams hw hd (LE.le.trans (Nat.le_add_right (ctr + OfNat.ofNat (nat_lit 50)) (OfNat.ofNat (nat_lit 2) * J)) hspace) hreport hout hfree hcover hwanted hcontrols hbank hcover20 hmasks hpairs (LE.le.trans (Nat.le_add_right (ae + OfNat.ofNat (nat_lit 2)) (OfNat.ofNat (nat_lit 2) * n)) hae) (LE.le.trans (Nat.add_le_add_left hnB bv) hbv) (LE.le.trans (Nat.le_add_right (be + OfNat.ofNat (nat_lit 2)) (OfNat.ofNat (nat_lit 2) * n)) hbe) (LE.le.trans (Nat.add_le_add_left hnC cv) hcv) (LE.le.trans (Nat.le_add_right (ce + OfNat.ofNat (nat_lit 2)) (OfNat.ofNat (nat_lit 2) * n)) hce) (LE.le.trans (Nat.le_add_right recs (OfNat.ofNat (nat_lit 4) * ThreeSum.ColorBandBounds.count n g)) hrec) howner hval hnB hnC (LE.le.trans hGA hnA) (LE.le.trans hGB hnB) (LE.le.trans hGC hnC) hnword hJword hhword hKword hgword hMword hlword hsword hRword hNword hReq hownerZ readCover readWanted readControls readBank readN readAE readB readBE readC readCE readRecs readVals readH readJ readM readG readGA readGB readGC readNB readNC readCount readPairs readLevels readLayers readSchedule readMasks hscan) hscan) readMasks) readSchedule) readLayers)
                                                                                                                                                                                                                                            readNC)
                                                                                                                                                                                                                                        readNB)
                                                                                                                                                                                                                                    readGC)
                                                                                                                                                                                                                                readGB)
                                                                                                                                                                                                                            readGA)
                                                                                                                                                                                                                  readG)
                                                                                                                                                                                                              readJ)
                                                                                                                                                                                                          readH)
                                                                                                                                                                                          readVals)
                                                                                                                                                                                      readRecs)
                                                                                                                                                                                  readCE)
                                                                                                                                                                              readC)
                                                                                                                                                                          readBE)
                                                                                                                                                                      readB)
                                                                                                                                                                  readAE)
                                                                                                                                                readN)
                                                                                                                                            readBank)
                                                                                                                                        readControls)
                                                                                                                                    readWanted)
                                                                                                                                readCover)
                                                                                            hvals)
                                                                                        hrec)
                                                                                    hce)
                                                                                hcv)
                                                                            hbe)
                                                                        hbv)
                                                                    hae)
                                                hR)
                                        hmasks)
                                    hbank)
                                hcontrols)
                            hwanted)
              hcover)
          hfree)
    hreport


end ThreeSum.LightThreeSumWantedHost

end


theorem solution : ∀ {lim : Light.Limits} {d T : Nat} {μ : Nat → Int} {free n params : Nat}
  {color :
    ThreeSum.Coloring.Parameter
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.Scales.inputBits n)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
  {x : Fin n → Int} {A B C : List.{0} Int}
  {hsA : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) A}
  {hsB : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) B}
  {hsC : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) C}
  {Q : Int → (Nat → Int) → Prop} (H : ThreeSum.ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
  (Hparams : Light.Seg μ params (ThreeSum.LightParameterInit.values n))
  (hparams :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) params
        (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19))))
      free)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd : @LT.lt.{0} Nat instLTNat d lim.depth)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC)
          (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n))))
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightThreeSumWantedHost.word n)) lim.word)
  (hscan :
    Light.Meets lim ThreeSum.LightReportingWantedScan.program
      (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152)))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (ThreeSum.LightReportingWantedDispatch.arguments (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC)
        (ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC))
      μ T Q),
  Light.Meets lim ThreeSum.LightThreeSumWantedHost.program
    (@OfNat.ofNat.{0} Nat (nat_lit 153) (instOfNatNat (nat_lit 153))) d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt params)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt free)
          (@List.cons.{0} Int
            (@Nat.cast.{0} Int instNatCastInt (ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC))
            (@List.cons.{0} Int
              (@Nat.cast.{0} Int instNatCastInt (ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC))
              (@List.nil.{0} Int))))))
    μ
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) T
      (@OfNat.ofNat.{0} Nat (nat_lit 4000) (instOfNatNat (nat_lit 4000))))
    Q := by
  exact @ThreeSum.LightThreeSumWantedHost.program_meets_sourceProof

#print axioms solution
