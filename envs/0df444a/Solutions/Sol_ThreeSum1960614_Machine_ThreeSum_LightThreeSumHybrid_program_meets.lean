-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybrid.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:15:30.051877+00:00
-- url     : https://prove2.me/submissions/905060d5-ca8f-48fc-97c1-fb19090f6aa4

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightThreeSumColor_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightThreeSumFastDriver_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightThreeSumHybridCore_program_meets

local instance platformRadixNonzero_b566b197f3 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Filter
end Filter
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters
namespace ThreeSum.LightColorParametersCosts
end ThreeSum.LightColorParametersCosts
namespace ThreeSum.LightThreeSumColor
end ThreeSum.LightThreeSumColor
namespace ThreeSum.LightThreeSumColorDriver
end ThreeSum.LightThreeSumColorDriver
namespace ThreeSum.LightThreeSumConcreteFast
end ThreeSum.LightThreeSumConcreteFast
namespace ThreeSum.LightThreeSumFastDriver
end ThreeSum.LightThreeSumFastDriver
namespace ThreeSum.LightThreeSumHybrid
end ThreeSum.LightThreeSumHybrid
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts
namespace ThreeSum.ThreeSumFastResourcesDriver
end ThreeSum.ThreeSumFastResourcesDriver
namespace ThreeSum.ThreeSumFastResourcesHybrid
end ThreeSum.ThreeSumFastResourcesHybrid
namespace ThreeSum.ThreeSumWantedHostConditions
end ThreeSum.ThreeSumWantedHostConditions
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.ColorClassLists
end ThreeSum1960614.Machine.ThreeSum.ColorClassLists
namespace ThreeSum1960614.Machine.ThreeSum.ColorParameters
end ThreeSum1960614.Machine.ThreeSum.ColorParameters
namespace ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts
end ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumColor
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumColor
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumConcreteFast
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumConcreteFast
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybrid
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybrid
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
end ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesDriver
end ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesDriver
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid
end ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
end ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions
end ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions
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



/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩







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
# Close the actual color decoder and scan around a concrete color program

The supplied program stays at its original indices. Four actual procedures
are appended: the six-cell decoder, scalar division, recursive short-circuit
scan, and parameter-header reader. The resulting program can then be
relocated by the already verified general relocation theorem.
-/

namespace ThreeSum.LightThreeSumColorDriver
open _root_.ThreeSum.LightThreeSumColorDriver


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.ColorParameters
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorParameters
open _root_.ThreeSum.LightColorParametersCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts

set_option maxHeartbeats 2000000
set_option maxRecDepth 14000





theorem program_length (colorProgram : _root_.ThreeSum1960614.Machine.Light.Program) (pColor : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.program colorProgram pColor).length=colorProgram.length+4 := by simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.program,_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.extra]





end ThreeSum.LightThreeSumColorDriver

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
# Initialize parameters once and execute the complete color family

The public arguments are [source,n,free]. The nineteen-cell parameter
record starts at free; the reusable six-cell color row starts at free+19;
the concrete selected-color program receives free+25 as its work boundary.
-/

namespace ThreeSum.LightThreeSumFastDriver
open _root_.ThreeSum.LightThreeSumFastDriver


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 2200000
set_option maxRecDepth 18000












theorem libraries_length (colorProgram : _root_.ThreeSum1960614.Machine.Light.Program) (pColor : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.libraries colorProgram pColor).length=colorProgram.length+26 := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.libraries,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program,List.length_append,List.length_map,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.program_length]
  change 22+(colorProgram.length+4)=colorProgram.length+26
  omega

theorem program_length (colorProgram : _root_.ThreeSum1960614.Machine.Light.Program) (pColor : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.program colorProgram pColor).length=colorProgram.length+27 := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.program,List.length_append,List.length_cons,List.length_nil,_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.libraries_length]







end ThreeSum.LightThreeSumFastDriver

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Uniform size conditions and original-color semantics for the wanted consumer

The cutoff is chosen before any memory, color, or original array. The
auxiliary-prime separation premise is proved for the actual generated pool.
-/

namespace ThreeSum.ThreeSumWantedHostConditions
open _root_.ThreeSum.ThreeSumWantedHostConditions


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.Filter
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
open scoped _root_.Topology

set_option maxHeartbeats 1600000
set_option maxRecDepth 12000









theorem ready_of_cutoff_le {k n : ℕ} (hn : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.cutoff k≤n) : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.Ready k n :=
  Classical.choose_spec (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.exists_cutoff k) n hn







end ThreeSum.ThreeSumWantedHostConditions

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Execute a complete selected color of the original input

The fixed355 prefixProgram prepares the actual encoding and shared source bank.
The fixed154 header caller then executes the physical wanted scan. Their
verified semantic and time connections yield the original color witness.
-/

namespace ThreeSum.LightThreeSumColor
open _root_.ThreeSum.LightThreeSumColor


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions
open _root_.ThreeSum.SharedTraversalCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts

set_option maxHeartbeats 2800000
set_option maxRecDepth 18000







theorem program_length : _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColor.program.length=510 := rfl



end ThreeSum.LightThreeSumColor

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Execute the complete fast driver from its concrete polynomial Need -/

namespace ThreeSum.ThreeSumFastResourcesDriver
open _root_.ThreeSum.ThreeSumFastResourcesDriver


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1700000
set_option maxRecDepth 17000

theorem program_meets {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {colorProgram : _root_.ThreeSum1960614.Machine.Light.Program} {pColor : ℕ}
    {src n free U colorTime d : ℕ} (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesDriver.need n U).Ok lim free d) (hsrc : src+n≤free)
    (hinput : _root_.ThreeSum1960614.Machine.Light.Seg μ src (List.ofFn x))
    (hcolor : _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.ColorLaw lim colorProgram pColor _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.need
      src n free (_root_.ThreeSum.LightThreeSumFastDriver.row free) U colorTime x) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.program colorProgram pColor) (colorProgram.length+26) d
      [src,n,free] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.time colorTime n)
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ _root_.ThreeSum.Coloring.DistinctZeroSum x) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ξ free) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.program_meets x μ H hsrc hinput hcolor



theorem program_meets_510 {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {colorProgram : _root_.ThreeSum1960614.Machine.Light.Program} {pColor : ℕ}
    {src n free U colorTime d : ℕ} (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (hlen : colorProgram.length=510) (H : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesDriver.need n U).Ok lim free d) (hsrc : src+n≤free)
    (hinput : _root_.ThreeSum1960614.Machine.Light.Seg μ src (List.ofFn x))
    (hcolor : _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.ColorLaw lim colorProgram pColor _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.need
      src n free (_root_.ThreeSum.LightThreeSumFastDriver.row free) U colorTime x) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.program colorProgram pColor) 536 d
      [src,n,free] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.time colorTime n)
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ _root_.ThreeSum.Coloring.DistinctZeroSum x) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ξ free) := by
  simpa only [hlen] using _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesDriver.program_meets x μ H hsrc hinput hcolor

end ThreeSum.ThreeSumFastResourcesDriver

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The concrete537-procedure fast solver

The actual selected-color executable supplies the color law of the closed
driver. The parameter header is built once, followed by one reusable color
row and the reusable selected-color allocation.
-/

namespace ThreeSum.LightThreeSumConcreteFast
open _root_.ThreeSum.LightThreeSumConcreteFast


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions
open _root_.ThreeSum.SharedTraversalCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts

set_option maxHeartbeats 1800000
set_option maxRecDepth 16000







theorem program_length : _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumConcreteFast.program.length=537 := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumConcreteFast.program,_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.program_length,_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColor.program_length]

/-- Every color call is the verified concrete510 executable, including its
    original-input witness equivalence and preservation of the input prefix. -/
theorem color_law {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {src n params row k : ℕ} (x : Fin n→ℤ)
    (hn : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.Ready k n) (hsrc : src+n≤row+6) (hparams : params+19≤row+6)
    (hx : ∀ i, |x i|≤((n^k : ℕ) : ℤ)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColorDriver.ColorLaw lim _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColor.program 509
      _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.need src n params row (n^k) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.colorBudget k n) x := by
  intro color ν dd hok hread hparameters hcolor
  apply (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColor.program_meets color x hn hsrc hparams le_rfl hok
    hread hx hparameters hcolor).mono le_rfl
  intro r ξ H
  exact ⟨H.1,H.2.1,fun a ha => H.2.2 a (by omega)⟩

/-- The full concrete driver returns exactly the original distinct-zero-sum
    decision whenever the proved uniform size conditions hold. -/
theorem program_meets {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {src n free k d : ℕ}
    (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (hn : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.Ready k n) (H : (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumConcreteFast.need n (n^k)).Ok lim free d)
    (hsrc : src+n≤free) (hinput : _root_.ThreeSum1960614.Machine.Light.Seg μ src (List.ofFn x))
    (hx : ∀ i, |x i|≤((n^k : ℕ) : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumConcreteFast.program 536 d [src,n,free] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumConcreteFast.time k n)
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ _root_.ThreeSum.Coloring.DistinctZeroSum x) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ξ free) := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesDriver.program_meets_510 x μ _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColor.program_length
    H hsrc hinput
  apply _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumConcreteFast.color_law x hn _ _ hx
  · unfold _root_.ThreeSum.LightThreeSumFastDriver.row
    omega
  · unfold _root_.ThreeSum.LightThreeSumFastDriver.row
    omega

noncomputable section









end
end ThreeSum.LightThreeSumConcreteFast

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







theorem fast_at_depth_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {κ cutoff n U free d e : ℕ}
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.need κ cutoff n U).Ok lim free d) (he : e≤d+2) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesDriver.need n (n^κ)).Ok lim free e :=
  H.mono (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.need]; omega) (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.need]; omega)
    (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.need]; omega)

theorem fast_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {κ cutoff n U free d : ℕ}
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.need κ cutoff n U).Ok lim free d) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesDriver.need n (n^κ)).Ok lim free (d+1) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.fast_at_depth_of_ok H (by omega)















end ThreeSum.ThreeSumFastResourcesHybrid

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybrid

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSumApsp.Spec
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.Spec
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
open _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybrid

section

/-- No execution or correctness callback remains: the successful guards
    supply the proved conditions of the actual concrete fast driver. -/
theorem ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybrid.program_meets__implementation_58cc6af4e8 {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {κ src n U free d : ℕ}
    (x : Fin n→ℤ) (μ : ℕ→ℤ) (hn : 0<n)
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybrid.need κ n U).Ok lim free d)
    (hsrc : src+n≤free) (hinput : _root_.ThreeSum1960614.Machine.Light.Seg μ src (List.ofFn x))
    (hx : ∀ i, |x i|≤(U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybrid.program κ) 542 d [n,U,src,free] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybrid.time κ n U)
      (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ _root_.ThreeSum.Coloring.DistinctZeroSum x) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) := by
  have hread : ∀ i : Fin n, μ (src+i.val)=x i := by
    intro i
    have hi : i.val<(List.ofFn x).length := by simpa only [List.length_ofFn] using i.isLt
    have hh : μ (src+i.val)=(List.ofFn x)[i.val] := hinput i.val hi
    simpa only [List.getElem_ofFn] using hh
  refine _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybridCore.program_meets _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumConcreteFast.program_length
    x μ hn hsrc H hread hx ?_
  intro hcutoff hU
  apply _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumConcreteFast.program_meets x μ
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.ready_of_cutoff_le hcutoff)
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.fast_of_ok H) hsrc hinput
  intro i
  exact (hx i).trans (Int.ofNat_le.mpr hU)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybrid.program_meets__implementation_58cc6af4e8) := (@ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybrid.program_meets__implementation_58cc6af4e8)

#print axioms solution
