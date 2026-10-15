-- Prove2me | solution 1 for ThreeSum.LightThreeSumHybrid.solves
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T19:23:20.673474+00:00
-- url     : https://prove2.me/submissions/56abc4d6-fb00-434f-a85d-198228a4d023

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_LightThreeSumHybrid_program_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters
namespace ThreeSum.LightColorParametersCosts
end ThreeSum.LightColorParametersCosts
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.ThreeSumReportingSetupData
end ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum.ThreeSumWantedHostConditions
end ThreeSum.ThreeSumWantedHostConditions
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec

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








/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩











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











































end

end Light

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

/-- What holds for the default and for every member of a list holds for every `getD`. -/
theorem getD_of_forall_mem {p : α → Prop} {l : List α} {d : α} (hd : p d) (h : ∀ x ∈ l, p x)
    (i : ℕ) : p (l.getD i d) := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem l d hi]
    exact h _ (List.getElem_mem hi)
  · rwa [List.getD_eq_default l d hi]























































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














/-- A bound on the absolute values of all members bounds every `getD` with default `0`. -/
theorem AbsLe.abs_getD_le {l : List ℤ} {U : ℤ} (hU : 0 ≤ U) (h : AbsLe l U) (i : ℕ) :
    |l.getD i 0| ≤ U :=
  List.getD_of_forall_mem (p := fun x => |x| ≤ U) (by rwa [abs_zero]) h i

/-! ## The entrywise sum of lists -/






















end ThreeSumApsp

end
end

section


/-! # Exact original-position semantics at the benchmark task boundary -/

namespace ThreeSum.OriginalThreeSum

open Light ThreeSumApsp.Spec

theorem distinct_iff_end {n : ℕ} (x : Fin n → ℤ) :
    Coloring.DistinctZeroSum x ↔ EndStatement.ThreeSum.yes x := by
  constructor
  · rintro ⟨i,j,k,hij,hik,hjk,hzero⟩
    exact ⟨i,j,k,hij,hjk,hik,hzero⟩
  · rintro ⟨i,j,k,hij,hjk,hik,hzero⟩
    exact ⟨i,j,k,hij,hik,hjk,hzero⟩

theorem flag_of_decision {n : ℕ} (x : Fin n → ℤ) {r : ℤ}
    (hbool : r=0 ∨ r=1) (hcorrect : r=1 ↔ Coloring.DistinctZeroSum x) :
    r=ThreeSumApsp.flag (ThreeSumApsp.ThreeSum x) := by
  by_cases hx : Coloring.DistinctZeroSum x
  · rw [ThreeSumApsp.flag_of ((distinct_iff_end x).mp hx)]
    exact hcorrect.mpr hx
  · rw [ThreeSumApsp.flag_of_not (fun h => hx ((distinct_iff_end x).mpr h))]
    rcases hbool with h | h
    · exact h
    · exact False.elim (hx (hcorrect.mp h))

theorem task_read {x : VecInst} {μ : ℕ → ℤ} {fr : ℕ} (H : x.Pre μ fr) :
    ∀ i : Fin x.N, μ (x.a+i.val)=vecOf x.N x.X i := by
  intro i
  exact H.seg.getD (by rw [H.len]; exact i.isLt) 0

theorem task_bound {x : VecInst} {μ : ℕ → ℤ} {fr : ℕ} (H : x.Pre μ fr) :
    ∀ i : Fin x.N, |vecOf x.N x.X i| ≤ (x.U : ℤ) := by
  intro i
  exact ThreeSumApsp.AbsLe.abs_getD_le (Int.natCast_nonneg _) H.le i.val

theorem task_post {x : VecInst} {μ ν : ℕ → ℤ} {fr : ℕ} {r : ℤ}
    (hbool : r=0 ∨ r=1) (hcorrect : r=1 ↔ Coloring.DistinctZeroSum (vecOf x.N x.X))
    (hkeep : Kept μ ν fr) : s3Task.Post x μ fr r ν :=
  ⟨flag_of_decision _ hbool hcorrect,hkeep⟩

end ThreeSum.OriginalThreeSum

end

section


/-!
# A complete original-input solver for the finite exceptional sizes

This four-procedure program checks every original-position triple and all
three inequalities between its indices. Its time is polynomial but is not
the target subquadratic bound. It supplies the exact fallback needed before
the asymptotic parameter regime, with no hypothesis on the integer values
beyond the task's given magnitude bound.
-/

namespace ThreeSum.LightBruteThreeSum

open Light ThreeSumApsp.Spec

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000












theorem program_length : program.length=4 := rfl

variable {lim : Limits} {P : Program}
































































end ThreeSum.LightBruteThreeSum

end

section


/-!
# Execute a complete selected color of the original input

The fixed355 prelude prepares the actual encoding and shared source bank.
The fixed154 header caller then executes the physical wanted scan. Their
verified semantic and time connections yield the original color witness.
-/

namespace ThreeSum.LightThreeSumColor

open Light Scales BandScales ThreeSumReportingSetupData
open ThreeSumWantedHostConditions SharedTraversalCosts

set_option maxHeartbeats 2800000
set_option maxRecDepth 18000











theorem program_length : program.length=510 := rfl





















































end ThreeSum.LightThreeSumColor

end

section


/-!
# Close the actual color decoder and scan around a concrete color program

The supplied program stays at its original indices. Four actual procedures
are appended: the six-cell decoder, scalar division, recursive short-circuit
scan, and parameter-header reader. The resulting program can then be
relocated by the already verified general relocation theorem.
-/

namespace ThreeSum.LightThreeSumColorDriver

open Light ColorParameters LightColorParametersCosts

set_option maxHeartbeats 2000000
set_option maxRecDepth 14000








theorem program_length (colorProgram : Program) (pColor : ℕ) :
    (program colorProgram pColor).length=colorProgram.length+4 := by simp [program,extra]




































end ThreeSum.LightThreeSumColorDriver

end

section


/-!
# Initialize parameters once and execute the complete color family

The public arguments are [source,n,free]. The nineteen-cell parameter
record starts at free; the reusable six-cell color row starts at free+19;
the concrete selected-color program receives free+25 as its work boundary.
-/

namespace ThreeSum.LightThreeSumFastDriver

open Light

set_option maxHeartbeats 2200000
set_option maxRecDepth 18000



















theorem libraries_length (colorProgram : Program) (pColor : ℕ) :
    (libraries colorProgram pColor).length=colorProgram.length+26 := by
  simp only [libraries,ReportingHostRelocation.program,List.length_append,List.length_map,
    LightThreeSumColorDriver.program_length]
  change 22+(colorProgram.length+4)=colorProgram.length+26
  omega

theorem program_length (colorProgram : Program) (pColor : ℕ) :
    (program colorProgram pColor).length=colorProgram.length+27 := by
  simp only [program,List.length_append,List.length_cons,List.length_nil,libraries_length]

















































end ThreeSum.LightThreeSumFastDriver

end

section


/-!
# The concrete537-procedure fast solver

The actual selected-color executable supplies the color law of the closed
driver. The parameter header is built once, followed by one reusable color
row and the reusable selected-color allocation.
-/

namespace ThreeSum.LightThreeSumConcreteFast

open Light Scales StageBounds ThreeSumWantedHostConditions SharedTraversalCosts

set_option maxHeartbeats 1800000
set_option maxRecDepth 16000









theorem program_length : program.length=537 := by
  rw [program,LightThreeSumFastDriver.program_length,LightThreeSumColor.program_length]































noncomputable section














end
end ThreeSum.LightThreeSumConcreteFast

end

section


/-!
# Exact assembly and execution of the final hybrid caller

The supplied first537 procedures are followed by the relocated four-procedure
original-triple solver, one integer-power procedure, and the hybrid caller.
The two runtime guards use the actual size and the supplied magnitude bound.
-/

namespace ThreeSum.LightThreeSumHybridCore

open Light

set_option maxHeartbeats 1400000
set_option maxRecDepth 18000















theorem libraries_length {fastP : Program} (hlen : fastP.length=537) :
    (libraries fastP).length=541 := by
  simp only [libraries,ReportingHostRelocation.program,List.length_append,
    List.length_map,hlen,LightBruteThreeSum.program_length]






theorem main_lookup {fastP : Program} (hlen : fastP.length=537) (κ cutoff : ℕ) :
    (program fastP κ cutoff)[542]?=some (body κ cutoff) := by
  have hh : (libraries fastP++[LightNatPower.body,body κ cutoff])[(libraries fastP).length+1]?=
      some (body κ cutoff) := by
    apply getElem?_append_length_add
    rfl
  simpa only [program,libraries_length hlen] using hh





























































































end ThreeSum.LightThreeSumHybridCore

end

section


/-!
# The complete543-procedure original-input solver

For each fixed magnitude exponent, the cutoff is chosen from the proved
uniform parameter conditions. The program tests that cutoff, computes the
integer power, and uses the exact original-triple fallback whenever needed.
Every branch returns the original distinct-position decision and preserves
all memory before the supplied free address.
-/

namespace ThreeSum.LightThreeSumHybrid

open Light ThreeSumApsp.Spec

set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

noncomputable section















theorem main_lookup (κ : ℕ) :
    (program κ)[542]?=some
      (LightThreeSumHybridCore.body κ (ThreeSumWantedHostConditions.cutoff κ)) :=
  LightThreeSumHybridCore.main_lookup LightThreeSumConcreteFast.program_length κ
    (ThreeSumWantedHostConditions.cutoff κ)



























/-- The complete executable solves the original task in every appended
    program, with the exact frozen hybrid time and affine resource need. -/
theorem solves_sourceProof (κ : ℕ) : Solves s3Task (program κ) 542 (time κ) (need κ) := by
  refine ⟨LightThreeSumHybridCore.body κ (ThreeSumWantedHostConditions.cutoff κ),
    main_lookup κ,fun R lim d x μ free H hok => ?_⟩
  have hp := getElem?_append_of_eq_some (main_lookup κ) R
  have hinput : Seg μ x.a (List.ofFn (vecOf x.N x.X)) := by
    intro i hi
    have hi' : i<x.N := by simpa only [List.length_ofFn] using hi
    simpa only [List.getElem_ofFn] using (OriginalThreeSum.task_read H) ⟨i,hi'⟩
  have hh := (program_meets (κ := κ) (d := d) (vecOf x.N x.X) μ H.N_pos hok
    H.below hinput (OriginalThreeSum.task_bound H)).append R
  obtain ⟨b,hb,he⟩ := hh.mono le_rfl (fun r ν ⟨hbool,hcorrect,hkept⟩ =>
    OriginalThreeSum.task_post (x := x) (μ := μ) (ν := ν) (fr := free)
      hbool hcorrect hkept)
  have heq : b=LightThreeSumHybridCore.body κ (ThreeSumWantedHostConditions.cutoff κ) :=
    Option.some.inj (hb.symm.trans hp)
  subst b
  exact he

end
end ThreeSum.LightThreeSumHybrid

end


theorem solution : ∀ (κ : Nat),
  Light.Solves Light.s3Task (ThreeSum.LightThreeSumHybrid.program κ)
    (@OfNat.ofNat.{0} Nat (nat_lit 542) (instOfNatNat (nat_lit 542))) (ThreeSum.LightThreeSumHybrid.time κ)
    (ThreeSum.LightThreeSumHybrid.need κ) := by
  exact @ThreeSum.LightThreeSumHybrid.solves_sourceProof

#print axioms solution
