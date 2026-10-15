-- Prove2me | solution 1 for ThreeSum.LightThreeSumHybrid.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T19:12:02.791597+00:00
-- url     : https://prove2.me/submissions/87400fd8-8c19-45fd-b755-736b64cb9030

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
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_LightThreeSumColor_program_meets
import Theorems.Thm_ThreeSum_LightThreeSumFastDriver_program_meets
import Theorems.Thm_ThreeSum_LightThreeSumHybridCore_program_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters
namespace ThreeSum.LightColorParametersCosts
end ThreeSum.LightColorParametersCosts
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
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
namespace ThreeSumApsp
end ThreeSumApsp
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



































/-! ## The rules -/






/-- More time and a weaker conclusion. -/
theorem Ends.mono {s σ T T' Q Q'} (h : Ends lim P d s σ T Q) (hT : T ≤ T')
    (hQ : ∀ σ', Q σ' → Q' σ') : Ends lim P d s σ T' Q' := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc.trans hT, hQ _ hq⟩



























































































































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














































end Light

end
end

section


/-!
# Uniform size conditions and original-color semantics for the wanted consumer

The cutoff is chosen before any memory, color, or original array. The
auxiliary-prime separation premise is proved for the actual generated pool.
-/

namespace ThreeSum.ThreeSumWantedHostConditions

open Light Scales BandScales Filter RawIncidences BandRawA ColorClassLists
open scoped Topology

set_option maxHeartbeats 1600000
set_option maxRecDepth 12000





















theorem ready_of_cutoff_le {k n : ℕ} (hn : cutoff k≤n) : Ready k n :=
  Classical.choose_spec (exists_cutoff k) n hn





























































end ThreeSum.ThreeSumWantedHostConditions

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


/-! # Execute the complete fast driver from its concrete polynomial Need -/

namespace ThreeSum.ThreeSumFastResourcesDriver

open Light

set_option maxHeartbeats 1700000
set_option maxRecDepth 17000

theorem program_meets {lim : Limits} {colorProgram : Program} {pColor : ℕ}
    {src n free U colorTime d : ℕ} (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (H : (need n U).Ok lim free d) (hsrc : src+n≤free)
    (hinput : Seg μ src (List.ofFn x))
    (hcolor : LightThreeSumColorDriver.ColorLaw lim colorProgram pColor ThreeSumFastResourcesColor.need
      src n free (LightThreeSumFastDriver.row free) U colorTime x) :
    Meets lim (LightThreeSumFastDriver.program colorProgram pColor) (colorProgram.length+26) d
      [src,n,free] μ (LightThreeSumFastDriver.time colorTime n)
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ξ free) :=
  LightThreeSumFastDriver.program_meets x μ H hsrc hinput hcolor





theorem program_meets_510 {lim : Limits} {colorProgram : Program} {pColor : ℕ}
    {src n free U colorTime d : ℕ} (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (hlen : colorProgram.length=510) (H : (need n U).Ok lim free d) (hsrc : src+n≤free)
    (hinput : Seg μ src (List.ofFn x))
    (hcolor : LightThreeSumColorDriver.ColorLaw lim colorProgram pColor ThreeSumFastResourcesColor.need
      src n free (LightThreeSumFastDriver.row free) U colorTime x) :
    Meets lim (LightThreeSumFastDriver.program colorProgram pColor) 536 d
      [src,n,free] μ (LightThreeSumFastDriver.time colorTime n)
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ξ free) := by
  simpa only [hlen] using program_meets x μ H hsrc hinput hcolor

end ThreeSum.ThreeSumFastResourcesDriver

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

/-- Every color call is the verified concrete510 executable, including its
    original-input witness equivalence and preservation of the input prefix. -/
theorem color_law {lim : Limits} {src n params row k : ℕ} (x : Fin n→ℤ)
    (hn : Ready k n) (hsrc : src+n≤row+6) (hparams : params+19≤row+6)
    (hx : ∀ i, |x i|≤((n^k : ℕ) : ℤ)) :
    LightThreeSumColorDriver.ColorLaw lim LightThreeSumColor.program 509
      ThreeSumFastResourcesColor.need src n params row (n^k) (colorBudget k n) x := by
  intro color ν dd hok hread hparameters hcolor
  apply (LightThreeSumColor.program_meets color x hn hsrc hparams le_rfl hok
    hread hx hparameters hcolor).mono le_rfl
  intro r ξ H
  exact ⟨H.1,H.2.1,fun a ha => H.2.2 a (by omega)⟩

/-- The full concrete driver returns exactly the original distinct-zero-sum
    decision whenever the proved uniform size conditions hold. -/
theorem program_meets {lim : Limits} {src n free k d : ℕ}
    (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (hn : Ready k n) (H : (need n (n^k)).Ok lim free d)
    (hsrc : src+n≤free) (hinput : Seg μ src (List.ofFn x))
    (hx : ∀ i, |x i|≤((n^k : ℕ) : ℤ)) :
    Meets lim program 536 d [src,n,free] μ (time k n)
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ξ free) := by
  apply ThreeSumFastResourcesDriver.program_meets_510 x μ LightThreeSumColor.program_length
    H hsrc hinput
  apply color_law x hn _ _ hx
  · unfold LightThreeSumFastDriver.row
    omega
  · unfold LightThreeSumFastDriver.row
    omega

noncomputable section














end
end ThreeSum.LightThreeSumConcreteFast

end

section


/-! # Affine resources for the actual finite-cutoff hybrid

The fast branch uses the computed magnitude `n^κ`; the fallback retains
the supplied magnitude `U`. Both branches reuse the same free address.
The fixed cutoff and exponent are included among the actual scalar word
controls, together with every intermediate integer power.
-/

namespace ThreeSum.ThreeSumFastResourcesHybrid

open Light

set_option maxHeartbeats 1700000
set_option maxRecDepth 16000












theorem fast_at_depth_of_ok {lim : Limits} {κ cutoff n U free d e : ℕ}
    (H : (need κ cutoff n U).Ok lim free d) (he : e≤d+2) :
    (ThreeSumFastResourcesDriver.need n (n^κ)).Ok lim free e :=
  H.mono (by dsimp only [need]; omega) (by dsimp only [need]; omega)
    (by dsimp only [need]; omega)

theorem fast_of_ok {lim : Limits} {κ cutoff n U free d : ℕ}
    (H : (need κ cutoff n U).Ok lim free d) :
    (ThreeSumFastResourcesDriver.need n (n^κ)).Ok lim free (d+1) :=
  fast_at_depth_of_ok H (by omega)


















































end ThreeSum.ThreeSumFastResourcesHybrid

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





















/-- No execution or correctness callback remains: the successful guards
    supply the proved conditions of the actual concrete fast driver. -/
theorem program_meets_sourceProof {lim : Limits} {κ src n U free d : ℕ}
    (x : Fin n→ℤ) (μ : ℕ→ℤ) (hn : 0<n)
    (H : (need κ n U).Ok lim free d)
    (hsrc : src+n≤free) (hinput : Seg μ src (List.ofFn x))
    (hx : ∀ i, |x i|≤(U : ℤ)) :
    Meets lim (program κ) 542 d [n,U,src,free] μ (time κ n U)
      (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ν free) := by
  have hread : ∀ i : Fin n, μ (src+i.val)=x i := by
    intro i
    have hi : i.val<(List.ofFn x).length := by simpa only [List.length_ofFn] using i.isLt
    have hh : μ (src+i.val)=(List.ofFn x)[i.val] := hinput i.val hi
    simpa only [List.getElem_ofFn] using hh
  refine LightThreeSumHybridCore.program_meets LightThreeSumConcreteFast.program_length
    x μ hn hsrc H hread hx ?_
  intro hcutoff hU
  apply LightThreeSumConcreteFast.program_meets x μ
    (ThreeSumWantedHostConditions.ready_of_cutoff_le hcutoff)
    (ThreeSumFastResourcesHybrid.fast_of_ok H) hsrc hinput
  intro i
  exact (hx i).trans (Int.ofNat_le.mpr hU)
























end
end ThreeSum.LightThreeSumHybrid

end


theorem solution : ∀ {lim : Light.Limits} {κ src n U free d : Nat} (x : Fin n → Int) (μ : Nat → Int),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    (ThreeSum.LightThreeSumHybrid.need κ n U).Ok lim free d →
      @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src n) free →
        Light.Seg μ src (@List.ofFn.{0} Int n x) →
          (∀ (i : Fin n),
              @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (x i))
                (@Nat.cast.{0} Int instNatCastInt U)) →
            Light.Meets lim (ThreeSum.LightThreeSumHybrid.program κ)
              (@OfNat.ofNat.{0} Nat (nat_lit 542) (instOfNatNat (nat_lit 542))) d
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt U)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt free) (@List.nil.{0} Int)))))
              μ (ThreeSum.LightThreeSumHybrid.time κ n U) fun (r : Int) (ν : Nat → Int) =>
              And
                (Or (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
                  (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                (And
                  (Iff (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@ThreeSum.Coloring.DistinctZeroSum n x))
                  (Light.Kept μ ν free)) := by
  exact @ThreeSum.LightThreeSumHybrid.program_meets_sourceProof

#print axioms solution
