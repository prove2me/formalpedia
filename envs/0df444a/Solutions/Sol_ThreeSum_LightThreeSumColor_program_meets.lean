-- Prove2me | solution 1 for ThreeSum.LightThreeSumColor.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T19:00:32.950627+00:00
-- url     : https://prove2.me/submissions/b3b88ff7-293d-47a3-bec5-33e5d058c427

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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_BandPrimeChoice_modulus_score_bound
import Theorems.Thm_ThreeSum_BandRawA_mem_aIndices_iff_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_allProducts
import Theorems.Thm_ThreeSum_BandRawA_mem_row
import Theorems.Thm_ThreeSum_BandRawA_owner_weightedFalseCount
import Theorems.Thm_ThreeSum_BandWeightedScore_block_bound
import Theorems.Thm_ThreeSum_EncodedColorPipelineData_ordered
import Theorems.Thm_ThreeSum_EncodedColorReportingData_report_le_source_allocation
import Theorems.Thm_ThreeSum_LightEncodedColorReportingPipeline_program_meets
import Theorems.Thm_ThreeSum_LightLocalCoverMagnitude_rounds_bound
import Theorems.Thm_ThreeSum_LightPrimePool_prefix_increasing
import Theorems.Thm_ThreeSum_LightReportingWantedScanStored_program_meets
import Theorems.Thm_ThreeSum_LightThreeSumWantedHost_program_meets
import Theorems.Thm_ThreeSum_Scales_primeDepth_loss_bound
import Theorems.Thm_ThreeSum_Scales_scoreLoss_finite_bound
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_components
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_offset_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_threshold_le
import Theorems.Thm_ThreeSum_SharedTraversalCosts_prefix_time_le_dispatch_budget
import Theorems.Thm_ThreeSum_ThreeSumColorBudgets_wanted_count_le
import Theorems.Thm_ThreeSum_ThreeSumWantedHostCosts_physical_step_le
import Theorems.Thm_ThreeSum_ThreeSumWantedHostDecision_accepted_iff_witness


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
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
namespace ThreeSum.BandWeightedScore
end ThreeSum.BandWeightedScore
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.EncodedColorWantedConsumerData
end ThreeSum.EncodedColorWantedConsumerData
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.HierarchyScales
end ThreeSum.HierarchyScales
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.MassScales
end ThreeSum.MassScales
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.ReportingHostWantedConsumerData
end ThreeSum.ReportingHostWantedConsumerData
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum.ReportingHostWantedPhysical
end ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankData
end ThreeSum.SharedReportingBankData
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.Switch
end ThreeSum.Switch
namespace ThreeSum.ThreeSumReportingSetupData
end ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum.ThreeSumWantedHostConditions
end ThreeSum.ThreeSumWantedHostConditions
namespace ThreeSum.ThreeSumWantedHostData
end ThreeSum.ThreeSumWantedHostData
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales
namespace ThreeSum.WantedRecordOrder
end ThreeSum.WantedRecordOrder
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

/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩

/-- A specification holds with every larger bound on the time. -/
theorem Meets.mono_time (h : Meets lim P p d vals μ T R) (hT : T ≤ T' := by omega) :
    Meets lim P p d vals μ T' R :=
  h.mono hT fun _ _ hR => hR






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































































/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]

























/-- A segment all of whose cells are kept. -/
theorem Seg.of_sameOn {K : ℕ → Prop} (h : Seg μ b l) (hs : SameOn K μ μ')
    (hK : ∀ i < l.length, K (b + i)) : Seg μ' b l := h.congr fun i hi => hs _ (hK i hi)





































































































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
























































































end ThreeSum.BandPartition

end

section


/-!
# A finite array minimum scan in the benchmark language

The selected index is a deterministic left-to-right minimum. Its value
can therefore instantiate the exact mean bound for offset balancing.
-/

namespace ThreeSum.LightMinimum

open Light





theorem least_lt (f : ℕ → ℤ) {n : ℕ} (hn : 0 < n) : least f n < n := by
  induction n with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero => simp [least]
      | succ n =>
          have h := ih (by omega)
          unfold least
          split <;> omega


































variable {lim : Limits} {P : Program} {d : ℕ}





































end ThreeSum.LightMinimum

end

section


/-!
# The aggregate weighted score of physical band-owner candidates

Each flagged owner contributes the score of its three actual truncated
bands. Owner multiplicities are retained. The contraction and initial bound
therefore apply to the same quadratic catalog that the program scans.
-/

namespace ThreeSum.BandWeightedScore

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
































































theorem partialScore_bound (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (k : ℕ)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j) :
    partialScore primes s q nA nB nC g A B C rs k ≤ k*(s*g^3) := by
  calc
    _ ≤ ∑ _i ∈ range k, s*g^3 := sum_le_sum fun i _ => block_bound primes s q nA nB nC g A B C _ hprime hinj
    _ = _ := by simp

theorem score_bound (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j) :
    score primes s q nA nB nC g A B C rs ≤ rs.length*(s*g^3) :=
  partialScore_bound primes s q nA nB nC g A B C rs rs.length hprime hinj


















































end ThreeSum.BandWeightedScore

end

section


/-!
# A common contracting modulus for the complete band-owner catalog

The same deterministic first-minimum rule is applied to the sum of every
flagged owner's score. These are joint choices for all bands, rather than
independent moduli whose contractions could not be combined.
-/

namespace ThreeSum.BandPrimeChoice

open BandCandidateRows BandWeightedScore Finset
open scoped BigOperators

set_option maxHeartbeats 1400000
set_option maxRecDepth 8000













theorem chosenIndex_lt (primes : ℕ → ℕ) {s q nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (hs : 0 < s) :
    chosenIndex primes s q nA nB nC g A B C rs < s := LightMinimum.least_lt _ hs
































theorem modulus_bounds (primes : ℕ → ℕ) {s nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (hs : 0 < s) (y Y r : ℕ)
    (hlo : ∀ i < s, y ≤ primes i) (hhi : ∀ i < s, primes i ≤ Y) :
    y^r ≤ modulus primes s nA nB nC g A B C rs r ∧
      modulus primes s nA nB nC g A B C rs r ≤ Y^r := by
  induction r with
  | zero => simp [modulus]
  | succ r ih =>
    have hidx := chosenIndex_lt (q := modulus primes s nA nB nC g A B C rs r)
      (nA := nA) (nB := nB) (nC := nC) (g := g) primes A B C rs hs
    constructor
    · simpa only [modulus,pow_succ,chosenPrime] using Nat.mul_le_mul ih.1 (hlo _ hidx)
    · simpa only [modulus,pow_succ,chosenPrime] using Nat.mul_le_mul ih.2 (hhi _ hidx)

theorem modulus_pos (primes : ℕ → ℕ) {s nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (hs : 0 < s)
    (hprime : ∀ i < s, Nat.Prime (primes i)) (r : ℕ) :
    0 < modulus primes s nA nB nC g A B C rs r := by
  have hh := (modulus_bounds (nA := nA) (nB := nB) (nC := nC) (g := g) primes A B C rs hs 1
    (Finset.sup (range s) primes) r
    (fun i hi => (hprime i hi).pos)
    (fun i hi => Finset.le_sup (mem_range.mpr hi))).1
  rw [one_pow] at hh
  omega

























































end ThreeSum.BandPrimeChoice

end

section


/-!
# Original-index incidences in the guarded global encoding

An incidence retains its original input indices, its complete sequence of
chosen-map occurrences and retained local edges, and its signed arithmetic
lift. Equal input values remain distinct original indices. The lift is
unique for a fixed original triple and representation, so it does not add
a factor of three to the representation bound.
-/

namespace ThreeSum.RawIncidences

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds
































































































































































































































section OriginalIndices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]














theorem mem_rawOn {h J : ℕ} {P d : ℤ} {T : Finset (Original α β γ)}
    {a : α → ℤ} {b : β → ℤ} {c : γ → ℤ} {r : RawItem h J α β γ} :
    r ∈ rawOn h J P d T a b c ↔
      r.1 ∈ T ∧ r.2 ∈ witnesses h J P d (a r.1.1) (b r.1.2.1) (c r.1.2.2) :=
  Finset.mem_sigma








































































































































































































end OriginalIndices

end ThreeSum.RawIncidences

end

section


/-!
# Exact relocation of closed verified procedure libraries

Every procedure call is shifted by the same list offset. The structural
execution proof preserves the exact initial/final states, runtime, memory
addresses, values, and depth budget. It permits composition of independently
verified fixed programs without assuming a new implementation contract.
-/

namespace ThreeSum.ReportingHostRelocation

open Light












theorem lookup {P : Program} {p : ℕ} {body : Stmt} (h : P[p]? = some body) (prefixProgram : Program) :
    (program prefixProgram P)[prefixProgram.length+p]? = some (relocate prefixProgram.length body) := by
  apply getElem?_append_length_add
  rw [List.getElem?_map,h]
  rfl

theorem exec {lim : Limits} {P : Program} {d : ℕ} {s : Stmt} {σ σ' : State} {c : ℕ}
    (h : Exec lim P d s σ σ' c) (prefixProgram : Program) :
    Exec lim (program prefixProgram P) d (relocate prefixProgram.length s) σ σ' c := by
  induction h with
  | skip => exact .skip
  | set h => exact .set h
  | store h₁ h₂ h₃ => exact .store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact .iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact .iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact .whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact .whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact .call h₁ (lookup h₂ prefixProgram) h₃ ih

theorem ends {lim : Limits} {P : Program} {d : ℕ} {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}
    (h : Ends lim P d s σ T Q) (prefixProgram : Program) :
    Ends lim (program prefixProgram P) d (relocate prefixProgram.length s) σ T Q := by
  obtain ⟨σ',c,he,hc,hq⟩ := h
  exact ⟨σ',c,exec he prefixProgram,hc,hq⟩

theorem meets {lim : Limits} {P : Program} {p d : ℕ} {vals : List ℤ} {μ : ℕ → ℤ}
    {T : ℕ} {R : ℤ → (ℕ → ℤ) → Prop} (h : Meets lim P p d vals μ T R) (prefixProgram : Program) :
    Meets lim (program prefixProgram P) (prefixProgram.length+p) d vals μ T R := by
  obtain ⟨body,hbody,he⟩ := h
  exact ⟨relocate prefixProgram.length body,lookup hbody prefixProgram,ends he prefixProgram⟩

end ThreeSum.ReportingHostRelocation

end

section


/-!
# Executing the candidate prime pool

This fixed program scans the integers in `(y,4*y]`, invokes the concrete
trial-division procedure, and writes every prime exactly once in increasing
order. The returned length and written array are the exact candidate pool
used by the contraction and auxiliary-weight theorems.
-/

namespace ThreeSum.LightPrimePool

open Light

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000





















































theorem prefix_nodup (y i : ℕ) : (scanned y i).Nodup :=
  (prefix_increasing y i).imp (fun h => Nat.ne_of_lt h)






theorem values_nodup (y : ℕ) : (values y).Nodup := prefix_nodup y (3*y)















theorem size_eq_card (y : ℕ) : size y = (PrimeDensity.candidates y).card := by
  rw [← values_toFinset,List.toFinset_card_of_nodup (values_nodup y)]
  rfl






theorem prime_spec {y i : ℕ} (hi : i < size y) :
    Nat.Prime (prime y i) ∧ y < prime y i ∧ prime y i ≤ 4*y :=
  mem_values.mp (prime_mem hi)

theorem prime_injective {y i j : ℕ} (hi : i < size y) (hj : j < size y)
    (heq : prime y i = prime y j) : i = j :=
  (List.getD_inj hi hj (values_nodup y)).mp heq







theorem values_nonempty {y : ℕ} (hy : 0 < y) : values y ≠ [] := by
  obtain ⟨p,hp,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul y hy.ne'
  have hmem : p ∈ values y := mem_values.mpr ⟨hp,hlo,by omega⟩
  intro heq
  simpa only [heq,List.not_mem_nil] using hmem

theorem size_pos {y : ℕ} (hy : 0 < y) : 0 < size y :=
  List.length_pos_iff.mpr (values_nonempty hy)


























































variable {lim : Limits} {P : Program} {d : ℕ}
























































































end ThreeSum.LightPrimePool

end

section


/-!
# Construct the prime pool and common contracting modulus from band records

The fixed host constructs the candidate prime array, then executes the
aggregate modulus chain on every owner record. The physical prime array and
every prefix modulus remain available to the encoder and reporting stages.
-/

namespace ThreeSum.LightBandPrimeConstruction

open Light BandCandidateRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000





theorem modulus_bounds {y nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (levels : ℕ) (hy : 0 < y) :
    y^levels ≤ modulus y nA nB nC g A B C rs levels ∧
      modulus y nA nB nC g A B C rs levels ≤ (4*y)^levels :=
  BandPrimeChoice.modulus_bounds (LightPrimePool.prime y) A B C rs
    (LightPrimePool.size_pos hy) y (4*y) levels
    (fun i hi => (LightPrimePool.prime_spec hi).2.1.le)
    (fun i hi => (LightPrimePool.prime_spec hi).2.2)

theorem modulus_score_bound {y nA nB nC g U : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (levels : ℕ) (hy : 1 < y)
    (hA : ∀ i < nA, |A i| ≤ (U : ℤ))
    (hB : ∀ i < nB, |B i| ≤ (U : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (U : ℤ)) :
    (LightPrimePool.size y)^levels * BandWeightedScore.score
      (LightPrimePool.prime y) (LightPrimePool.size y)
      (modulus y nA nB nC g A B C rs levels) nA nB nC g A B C rs ≤
      (Nat.log y (3*U))^levels * BandWeightedScore.score
        (LightPrimePool.prime y) (LightPrimePool.size y) 1 nA nB nC g A B C rs :=
  BandPrimeChoice.modulus_score_bound (LightPrimePool.prime y) (LightPrimePool.size y)
    nA nB nC g y U levels A B C rs hy (fun i hi => (LightPrimePool.prime_spec hi).1)
    (fun i hi j hj heq => LightPrimePool.prime_injective hi hj heq)
    (fun i hi => (LightPrimePool.prime_spec hi).2.1.le) hA hB hC
























variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs y levels free maxMod U : ℕ}



















































































end ThreeSum.LightBandPrimeConstruction

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









































































































theorem mem_firstRows {n g i : ℕ} {rs : List Record} {l : Label} :
    l ∈ firstRows n g rs i ↔
      l.owner < i ∧ l ∈ row n g l.owner (rs.getD l.owner default) := by
  constructor
  · intro hl
    obtain ⟨owner,ho,hl⟩ := List.mem_flatMap.mp hl
    have he := (mem_row.mp hl).2.1
    subst owner
    exact ⟨List.mem_range.mp ho,hl⟩
  · rintro ⟨ho,hl⟩
    exact List.mem_flatMap.mpr ⟨l.owner,List.mem_range.mpr ho,hl⟩
















































end ThreeSum.BandRawA

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

/-- A list below fr stays where it is if nothing below fr changes. -/
theorem Seg.of_kept {μ μ' : ℕ → ℤ} {a fr : ℕ} {l : List ℤ} (h : Seg μ a l) (hk : Kept μ μ' fr)
    (hle : a + l.length ≤ fr) : Seg μ' a l :=
  h.of_sameOn hk fun i hi => show a + i < fr by omega

/-! ## Tasks and solvers -/
























































































/-! ## Hosts -/






















/-! ## Tasks with a list of parameters -/














































end Light

end
end

section


/-!
# Physical incidence indices and their exact owner coordinates

An incidence at position `count owner + localA` retains that physical
owner and its sorted A coordinate. Every emitted index has exactly this
form, including equal values emitted by different owners.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows

set_option maxHeartbeats 1700000
set_option maxRecDepth 7000



































































theorem at_mem {n g k : ℕ} {rs : List Record}
    (hk : k < (items n g rs).length) : labelAt n g rs k ∈ items n g rs := by
  rw [labelAt,List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

theorem at_bounds {n g k : ℕ} {rs : List Record}
    (hk : k < (items n g rs).length) :
    (labelAt n g rs k).owner < rs.length ∧
      (ownerRecord n g rs k).flag=1 ∧
      BandPartition.start g (ownerRecord n g rs k).a ≤ (labelAt n g rs k).position ∧
      (labelAt n g rs k).position < BandPartition.stop n g (ownerRecord n g rs k).a := by
  have hh := mem_firstRows.mp (at_mem hk)
  have hr := mem_row.mp hh.2
  exact ⟨hh.1,hr.1,hr.2.2.1,hr.2.2.2⟩
























































end ThreeSum.BandRawA

end

section


/-!
# Each physical A incidence retains exactly its owner's B/C product

The products in this file are mathematical counting domains. The actual
catalog is still constructed by the verified quadratic owner loop and
linear band copies. Distinct owner products are disjoint because their
physical A incidence indices differ, even when their values coincide.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1900000
set_option maxRecDepth 8000



























































theorem mem_ownerProduct {nA nB nC g s : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (hs : s < rs.length) :
    t ∈ ownerProduct nA nB nC g rs s ↔
      t.1 < (items nA g rs).length ∧ (labelAt nA g rs t.1).owner=s ∧
        t.2.1 ∈ bandPositions nB g (rs.getD s default).b ∧
        t.2.2 ∈ bandPositions nC g (rs.getD s default).c := by
  simp only [ownerProduct,mem_product,mem_aIndices_iff_owner hs,and_assoc]

theorem ownerProduct_disjoint {nA nB nC g s t : ℕ} {rs : List Record}
    (hs : s < rs.length) (ht : t < rs.length) (hst : s ≠ t) :
    Disjoint (ownerProduct nA nB nC g rs s) (ownerProduct nA nB nC g rs t) := by
  apply disjoint_left.mpr
  intro x hx hy
  have hs' := (mem_ownerProduct hs).mp hx
  have ht' := (mem_ownerProduct ht).mp hy
  exact hst (hs'.2.1.symm.trans ht'.2.1)
















































theorem sum_allProducts (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List Record) :
    (∑ t ∈ allProducts nA nB nC g rs, F t)=
      ∑ s ∈ range rs.length, ∑ t ∈ ownerProduct nA nB nC g rs s, F t := by
  unfold allProducts
  apply sum_biUnion
  intro s hs t ht hst
  exact ownerProduct_disjoint (mem_range.mp hs) (mem_range.mp ht) hst





























end ThreeSum.BandRawA

end

section


/-!
# The aggregate prime score is the exact physical incidence-product score

The executable A catalog supplies the first-coordinate values. Its owner
metadata supplies the B/C slices. Thus the mathematical score summed by
the actual prime selector counts this same domain with all multiplicities.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1900000
set_option maxRecDepth 8000







































theorem all_weightedFalseCount (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) :
    Arithmetic.weightedFalseCount (allProducts nA nB nC g rs)
      (ModuloCounts.difference (valueAt nA g rs A) B C)
      (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux)) q=
      BandWeightedScore.score primes aux q nA nB nC g A B C rs := by
  unfold Arithmetic.weightedFalseCount
  rw [sum_allProducts]
  unfold BandWeightedScore.score BandWeightedScore.partialScore
  apply sum_congr rfl
  intro s hs
  exact owner_weightedFalseCount primes aux q nA nB nC g A B C rs (mem_range.mp hs)














































end ThreeSum.BandRawA

end

section


/-!
# The actual integer block schedule

All four size parameters below are executable natural-number functions.
The finite bounds and limits concern these functions, including the even
rounding of the cube root and the divisibility constraints on the number
of blocks.  No asymptotic size premise is imposed on the schedule.
-/

namespace ThreeSum.Scales

open Filter Real
open scoped Topology

















































































noncomputable section








































































































































































































































































































theorem primeDepth_upper (R : ℕ → ℕ) {n : ℕ} (hR : 4 ≤ R n) :
    4 * (4 * primeWindow n) ^ primeDepth R n ≤ R n := by
  have hr : R n / 4 ≠ 0 := by omega
  have h := Nat.pow_log_le_self (4 * primeWindow n) hr
  have h4 := Nat.mul_le_mul_left 4 h
  have hd := Nat.div_mul_le_self (R n) 4
  simpa [primeDepth, Nat.mul_comm] using h4.trans (by simpa [Nat.mul_comm] using hd)












































































































































































































































































































































































































































































































































end

end ThreeSum.Scales

end

section


/-!
# The executable band size and its exact exponent

The band numerator is the integer ceiling of the square root of the actual
typed output count. The denominator is `2^(mu/20)`. Since the block schedule
has `20 ∣ mu`, the denominator exponent has no divisibility error.
-/

namespace ThreeSum.BandScales

open Filter Real ThreeSum.Scales
open scoped Topology











theorem typedOutputs_pos (n : ℕ) : 0 < typedOutputs n := by
  unfold typedOutputs
  exact Nat.pow_pos (Nat.choose_pos (by omega))



























noncomputable section

































































































































end

end ThreeSum.BandScales

end

section


/-!
# Actual finite hierarchy counts

These are the binomial counts used by the concrete microblock hierarchy.
Every prefix partition is included.  The integer switch and its rounding
allowance are applied before any asymptotic estimate is made.  The counts
in this module are combinatorial work counts; the implementation's operation
counts, raw wanted incidences, and false-mass bounds are separate interfaces.
-/

namespace ThreeSum.CostLedger

open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch
open scoped Topology BigOperators

set_option maxHeartbeats 400000






















theorem bandCount_mul_bounds (n : ℕ) :
    n ≤ BandScales.bandSize n * bandCount n ∧
      BandScales.bandSize n * bandCount n < n + BandScales.bandSize n := by
  constructor
  · exact (ceilDiv_le_iff_le_mul (a := BandScales.bandSize n) (b := n)
      (c := bandCount n) (BandScales.bandSize_pos n)).mp le_rfl
  · have h := Nat.div_mul_le_self (n + BandScales.bandSize n - 1) (BandScales.bandSize n)
    simp only [bandCount, Nat.ceilDiv_eq_add_pred_div]
    rw [Nat.mul_comm (BandScales.bandSize n)]
    have hpos := BandScales.bandSize_pos n
    omega
















noncomputable section

















































































































































end
end ThreeSum.CostLedger

end

section


/-!
# Actual wanted-incidence and false-mass majorants

The numerator of the wanted bound retains all raw A occurrences, all three
arithmetic lifts, and every schedule occurrence.  The false bound uses the
actual candidate count, integer band count, score loss, and modulus loss.
No asymptotic premise about an input-dependent mass is assumed here: the
transfer lemmas take the explicit finite inequalities from the counting
and prime-chain algorithms.
-/

namespace ThreeSum.MassScales

open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.CostLedger ThreeSum.HierarchyScales
open scoped Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000



















































noncomputable section













































































































































theorem false_mass_le {n k P H H1 : ℕ}
    (hscore : P * H ≤ scoreLoss k n * H1)
    (hinit : H1 ≤ candidateCount n * rawTripleBound n)
    (hmod : radix n ≤ primeLoss radix n * P) :
    (H : ℝ) ≤ falseMajorant k n := by
  have hbound : H * radix n ≤ falseNumerator k n := by
    calc
      H * radix n ≤ primeLoss radix n * (P * H) := by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using Nat.mul_le_mul_left H hmod
      _ ≤ primeLoss radix n * (scoreLoss k n * H1) := Nat.mul_le_mul_left _ hscore
      _ ≤ primeLoss radix n * (scoreLoss k n * (candidateCount n * rawTripleBound n)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hinit)
      _ = falseNumerator k n := by unfold falseNumerator; ring
  rw [falseMajorant, le_div_iff₀ (show (0 : ℝ) < radix n by exact_mod_cast radix_pos n)]
  exact_mod_cast hbound

end
end ThreeSum.MassScales

end

section


/-!
# A uniform size-only budget for the six principal stage counts

Both mass budgets are executable integer divisions of the concrete size
majorants.  The final bound is uniform in the input-dependent masses: the
eventual size threshold is chosen before `W`, `H`, `P`, or `H1` are quantified.
This remains a theorem about the specified finite work quantities, not a
claim that a complete machine has been proved to execute within them.
-/

namespace ThreeSum.UniformStageBounds

open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales ThreeSum.StageBounds
open scoped Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000













noncomputable section

theorem false_le_budget {n k P H H1 : ℕ}
    (hscore : P * H ≤ scoreLoss k n * H1)
    (hinit : H1 ≤ candidateCount n * rawTripleBound n)
    (hmod : radix n ≤ primeLoss radix n * P) : H ≤ falseBudget k n := by
  have hr := false_mass_le hscore hinit hmod
  rw [falseMajorant, le_div_iff₀ (show (0 : ℝ) < radix n by exact_mod_cast radix_pos n)] at hr
  apply (Nat.le_div_iff_mul_le (radix_pos n)).mpr
  exact_mod_cast hr





















































































































end
end ThreeSum.UniformStageBounds

end

section


/-!
# Finite scale guarantees for the executed physical-owner modulus

These theorems instantiate the previously proved size-only mass bounds with
the common modulus actually constructed from the candidate record array.
The weighted count is over physical A incidences and their own B/C bands.
-/

namespace ThreeSum.BandPrimeScales

open BandCandidateRows Scales BandScales CostLedger

set_option maxHeartbeats 1600000
set_option maxRecDepth 9000



















theorem modulus_bounds (n nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List Record) :
    primeWindow n^primeDepth radix n ≤ modulus n nA nB nC A B C rs ∧
      modulus n nA nB nC A B C rs ≤ (4*primeWindow n)^primeDepth radix n :=
  LightBandPrimeConstruction.modulus_bounds A B C rs _ (by have := primeWindow_ge_two n; omega)

/-- The integer guard used by the three-lift residue construction. -/
theorem modulus_guard {n nA nB nC : ℕ} (A B C : ℕ → ℤ) (rs : List Record)
    (hR : 4 ≤ radix n) : 4*modulus n nA nB nC A B C rs ≤ radix n :=
  (Nat.mul_le_mul_left 4 (modulus_bounds n nA nB nC A B C rs).2).trans
    (primeDepth_upper radix hR)

theorem modulus_loss (n nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List Record) :
    radix n ≤ primeLoss radix n*modulus n nA nB nC A B C rs :=
  primeDepth_loss_bound radix (modulus_bounds n nA nB nC A B C rs).1









theorem score_contraction {k n nA nB nC : ℕ} (A B C : ℕ → ℤ) (rs : List Record)
    (hA : ∀ i < nA, |A i| ≤ (n^k : ℤ))
    (hB : ∀ i < nB, |B i| ≤ (n^k : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (n^k : ℤ)) :
    candidateCount n^primeDepth radix n * score n (modulus n nA nB nC A B C rs) nA nB nC A B C rs ≤
      divisorBudget k n^primeDepth radix n * score n 1 nA nB nC A B C rs := by
  have hh := LightBandPrimeConstruction.modulus_score_bound (y := primeWindow n)
    (g := bandSize n) (U := n^k) A B C rs (primeDepth radix n)
    (by have := primeWindow_ge_two n; omega)
    (by simpa only [Nat.cast_pow] using hA)
    (by simpa only [Nat.cast_pow] using hB)
    (by simpa only [Nat.cast_pow] using hC)
  simpa only [LightPrimePool.size_eq_card,candidateCount,divisorBudget,score,modulus] using hh

theorem initial_score_bound {n nA nB nC : ℕ} (A B C : ℕ → ℤ) (rs : List Record)
    (hcount : rs.length ≤ 3*bandCount n^2) :
    score n 1 nA nB nC A B C rs ≤ candidateCount n*MassScales.rawTripleBound n := by
  have hh := BandWeightedScore.score_bound (LightPrimePool.prime (primeWindow n))
    (LightPrimePool.size (primeWindow n)) 1 nA nB nC (bandSize n) A B C rs
    (fun _ hi => (LightPrimePool.prime_spec hi).1)
    (fun _ hi _ hj heq => LightPrimePool.prime_injective hi hj heq)
  calc
    _ ≤ rs.length*(LightPrimePool.size (primeWindow n)*bandSize n^3) := hh
    _ ≤ (3*bandCount n^2)*(LightPrimePool.size (primeWindow n)*bandSize n^3) :=
      Nat.mul_le_mul_right _ hcount
    _ = _ := by rw [LightPrimePool.size_eq_card]; unfold candidateCount MassScales.rawTripleBound; ring

theorem score_loss {k n nA nB nC : ℕ} (A B C : ℕ → ℤ) (rs : List Record)
    (hbudget : divisorBudget k n*primeWindow n ≤
      candidateCount n*(4*(k+2)*(inputBits n+1)))
    (hA : ∀ i < nA, |A i| ≤ (n^k : ℤ))
    (hB : ∀ i < nB, |B i| ≤ (n^k : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (n^k : ℤ)) :
    modulus n nA nB nC A B C rs*score n (modulus n nA nB nC A B C rs) nA nB nC A B C rs ≤
      scoreLoss k n*score n 1 nA nB nC A B C rs := by
  have hpos : 0 < (PrimeDensity.candidates (primeWindow n)).card := by
    rw [← LightPrimePool.size_eq_card]
    exact LightPrimePool.size_pos (by have := primeWindow_ge_two n; omega)
  exact scoreLoss_finite_bound hpos hbudget (score_contraction A B C rs hA hB hC)
    (modulus_bounds n nA nB nC A B C rs).2






























end ThreeSum.BandPrimeScales

end

section


/-!
# Bounded finite index types for the same physical owner products

The A type is the complete flattened incidence array; B and C are the
retained sorted arrays. Coordinate transport is injective and preserves
both each owner's product and its exact weighted collision score.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000




















theorem coordinates_injective {a b c : ℕ} :
    Function.Injective (@coordinates a b c) := by
  rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ he
  simp only [coordinates,Prod.mk.injEq] at he
  exact Prod.ext (Fin.ext he.1) (Prod.ext (Fin.ext he.2.1) (Fin.ext he.2.2))

@[simp] theorem mem_finiteAIndices {n g s : ℕ} {rs : List Record}
    {i : Fin (items n g rs).length} :
    i ∈ finiteAIndices n g rs s ↔ i.val ∈ aIndices n g rs s := by
  simp only [finiteAIndices,mem_filter,mem_univ,true_and]





@[simp] theorem mem_finiteOwnerProduct {nA nB nC g s : ℕ} {rs : List Record}
    {t : Fin (items nA g rs).length × Fin nB × Fin nC} :
    t ∈ finiteOwnerProduct nA nB nC g rs s ↔
      coordinates t ∈ ownerProduct nA nB nC g rs s := by
  simp only [finiteOwnerProduct,ownerProduct,mem_product,mem_finiteAIndices,
    mem_finiteBandPositions,coordinates]

@[simp] theorem mem_finiteAllProducts {nA nB nC g : ℕ} {rs : List Record}
    {t : Fin (items nA g rs).length × Fin nB × Fin nC} :
    t ∈ finiteAllProducts nA nB nC g rs ↔
      coordinates t ∈ allProducts nA nB nC g rs := by
  simp only [finiteAllProducts,mem_filter,mem_univ,true_and]













theorem allProducts_bounds {nA nB nC g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ allProducts nA nB nC g rs) :
    t.1 < (items nA g rs).length ∧ t.2.1 < nB ∧ t.2.2 < nC := by
  obtain ⟨ha,hb,hc⟩ := mem_allProducts.mp ht
  exact ⟨ha,bandPositions_lt hb,bandPositions_lt hc⟩








theorem finite_lift {nA nB nC g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ allProducts nA nB nC g rs) :
    ∃ u ∈ finiteAllProducts nA nB nC g rs, coordinates u=t := by
  obtain ⟨ha,hb,hc⟩ := allProducts_bounds ht
  refine ⟨(⟨t.1,ha⟩,⟨t.2.1,hb⟩,⟨t.2.2,hc⟩),?_,rfl⟩
  exact mem_finiteAllProducts.mpr ht
















theorem sum_finiteAllProducts (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List Record) :
    (∑ u ∈ finiteAllProducts nA nB nC g rs, F (coordinates u))=
      ∑ t ∈ allProducts nA nB nC g rs, F t := by
  refine sum_bij (fun u _ => coordinates u) ?_ ?_ ?_ ?_
  · intro u hu
    exact mem_finiteAllProducts.mp hu
  · intro u hu v hv he
    exact coordinates_injective he
  · intro t ht
    obtain ⟨u,hu,he⟩ := finite_lift ht
    exact ⟨u,hu,he⟩
  · intro u hu
    rfl














theorem finiteAll_weightedFalseCount (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) :
    Arithmetic.weightedFalseCount (finiteAllProducts nA nB nC g rs)
      (fun t => C t.2.2.val-B t.2.1.val-valueAt nA g rs A t.1.val)
      (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux)) q=
      BandWeightedScore.score primes aux q nA nB nC g A B C rs := by
  rw [← all_weightedFalseCount primes aux q nA nB nC g A B C rs]
  unfold Arithmetic.weightedFalseCount
  exact sum_finiteAllProducts
    (fun t => if (q : ℤ) ∣ ModuloCounts.difference (valueAt nA g rs A) B C t then
      Arithmetic.missWeight (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux))
        (ModuloCounts.difference (valueAt nA g rs A) B C t) else 0) nA nB nC g rs















end ThreeSum.BandRawA

end

section


/-!
# Exact sharing of source transforms and the encoder ledger

Source stages are indexed by a source band and an occurrence vector. The
output subset and the three-valued A lift do not enter the source function.
Compact table and zeta charges below match the existing `encoderCount`
without introducing a factor for all complete global outputs.
-/

namespace ThreeSum.BlockSourceSharing

open BlockEncoding GlobalEncoding BlockIndexedQuery SubsetAddress
open Scales TrimScales CostLedger StageBounds






































theorem width_eq (n : ℕ) :
    blockCount (inputBits n)*(512*microHalf (inputBits n)) = 256*mu n := by
  unfold mu totalSize microSize microHalf
  ring

































































end ThreeSum.BlockSourceSharing

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

theorem mem_items (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) (z : ℤ) :
    z ∈ items x color want scale n ↔ ∃ i, i < n ∧ color i = want ∧ scale*x i = z := by
  simp [items,and_assoc]





















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


/-!
# Owner queries are the exact fibers of the global physical domain

The A incidence fixes its owner. Restricting to that owner's B/C bands
therefore leaves the entire wanted fiber unchanged. The mass read by the
owner-local query is exactly the mass charged by the global dense guard.
-/

namespace ThreeSum.DenseGuardBands

open Finset GlobalEncoding RawIncidences RawReporting ReportingHostFrontierLayout

section General

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem domain_eq_of_first_fiber {h J : ℕ} {P shift : ℤ}
    (T U : Finset (Original α β γ)) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (w : Wanted h J α)
    (hf : ∀ t : Original α β γ, t.1=w.1 → (t ∈ T ↔ t ∈ U)) :
    domain (rawOn h J P shift T a b c) w=domain (rawOn h J P shift U a b c) w := by
  ext r
  simp only [domain,mem_filter,mem_rawOn]
  constructor
  · rintro ⟨⟨ht,hr⟩,he⟩
    have ha : r.1.1=w.1 := congrArg (fun z : Wanted h J α => z.1) he
    exact ⟨⟨(hf r.1 ha).mp ht,hr⟩,he⟩
  · rintro ⟨⟨hu,hr⟩,he⟩
    have ha : r.1.1=w.1 := congrArg (fun z : Wanted h J α => z.1) he
    exact ⟨⟨(hf r.1 ha).mpr hu,hr⟩,he⟩

end General

open BandRawA

theorem finite_owner_fiber {nA nB nC g s : ℕ} {rs : List BandCandidateRows.Record}
    (hs : s < rs.length) (i : Fin (items nA g rs).length)
    (hi : (BandRawA.labelAt nA g rs i.val).owner=s)
    (t : Fin (items nA g rs).length × Fin nB × Fin nC) (ht : t.1=i) :
    t ∈ finiteAllProducts nA nB nC g rs ↔ t ∈ finiteOwnerProduct nA nB nC g rs s := by
  have ho : (BandRawA.labelAt nA g rs t.1.val).owner=s := by rw [ht]; exact hi
  simp only [mem_finiteAllProducts,mem_finiteOwnerProduct,mem_allProducts,mem_ownerProduct hs,
    coordinates,ownerRecord,ho,true_and]

theorem domain_global_eq_owner {h J nA nB nC g s : ℕ} {P shift : ℤ}
    (rs : List BandCandidateRows.Record) (hs : s < rs.length)
    (a : Fin (items nA g rs).length→ℤ) (b : Fin nB→ℤ) (c : Fin nC→ℤ)
    (w : Wanted h J (Fin (items nA g rs).length))
    (ho : (BandRawA.labelAt nA g rs w.1.val).owner=s) :
    domain (rawOn h J P shift (finiteAllProducts nA nB nC g rs) a b c) w=
      domain (rawOn h J P shift (finiteOwnerProduct nA nB nC g rs s) a b c) w :=
  domain_eq_of_first_fiber _ _ a b c w (finite_owner_fiber hs w.1 ho)

theorem prefixQuery_global_eq_owner {h J nA nB nC g s k : ℕ} {P shift : ℤ}
    (rs : List BandCandidateRows.Record) (hs : s < rs.length)
    (a : Fin (items nA g rs).length→ℤ) (b : Fin nB→ℤ) (c : Fin nC→ℤ)
    (w : Wanted h J (Fin (items nA g rs).length))
    (ho : (BandRawA.labelAt nA g rs w.1.val).owner=s)
    (pre : List (Finset (Fin (512*h)))) :
    prefixQuery (rawOn h J P shift (finiteAllProducts nA nB nC g rs) a b c) w k pre=
      prefixQuery (rawOn h J P shift (finiteOwnerProduct nA nB nC g rs s) a b c) w k pre := by
  simp only [prefixQuery,domain_global_eq_owner rs hs a b c w ho]

theorem rootMass_global_eq_owner {h J nA nB nC g s : ℕ} {P shift : ℤ}
    (rs : List BandCandidateRows.Record) (hs : s < rs.length)
    (a : Fin (items nA g rs).length→ℤ) (b : Fin nB→ℤ) (c : Fin nC→ℤ)
    (w : Wanted h J (Fin (items nA g rs).length))
    (ho : (BandRawA.labelAt nA g rs w.1.val).owner=s) :
    rootMass (rawOn h J P shift (finiteAllProducts nA nB nC g rs) a b c) w=
      rootMass (rawOn h J P shift (finiteOwnerProduct nA nB nC g rs s) a b c) w :=
  prefixQuery_global_eq_owner rs hs a b c w ho []

end ThreeSum.DenseGuardBands

end

section


/-!
# Distinct wanted labels in the actual emitted array

The join's physical slots decode injectively, even when original integer
values or key values repeat. Consequently every prefix of the actual
array is a valid distinct-label input to the cumulative dense guard.
-/

namespace ThreeSum.DenseGuardWanted

open Light WantedRecordOrder












































































theorem labelAt_mem {μ : ℕ → ℤ} {free M P h J : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P xs)
      (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J) shift)
    (slot : Fin (μ free).toNat) : labelAt H slot ∈ RawAKeyLists.wanted M P xs h J shift := by
  obtain ⟨i,j,hi,_,hL,hR,hm⟩ := WantedRecordCoverage.output_pair H slot.isLt
  simpa only [labelAt,leftIndex,rightIndex,hL,hR,Int.toNat_natCast] using hm











end ThreeSum.DenseGuardWanted

end

section


/-!
# Original input to normalized color bands

This fixed program computes index colors, writes the three class arrays and
their headers, then reads those headers into the existing normalization and
owner-table program. All buffers and resource bounds depend on the original
input length, rather than on externally supplied color-class lengths.
-/

namespace ThreeSum.LightColorBands

open Light ColorClassLists

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000













theorem class_bounded {n W U : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) (hs : |scale| ≤ 1) (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    ∀ z ∈ classList p x c scale, |z| ≤ (U : ℤ) := by
  intro z hz
  obtain ⟨i,hi,_,rfl⟩ :=
    (LightClassFilter.mem_items (value x) (LightColorIndex.color p) c scale n z).mp hz
  have hv : |value x i| ≤ (U : ℤ) := by
    simpa only [value,hi,dite_true] using hx ⟨i,hi⟩
  rw [abs_mul]
  calc
    |scale| * |value x i| ≤ 1 * (U : ℤ) :=
      mul_le_mul hs hv (abs_nonneg _) (by norm_num)
    _ = (U : ℤ) := one_mul _








variable {lim : Limits} {P : Program} {d : ℕ}

























































































































end ThreeSum.LightColorBands

end

section


/-!
# Actual initialization of the integer block schedule

The fixed program computes all initial size parameters from the input
length. It uses the benchmark's proved logarithm, ceiling cube-root and
ceiling-half loops, with exact rounding bridges below. Division is used
only through an actual counting routine on the logarithmic numerator.
-/

namespace ThreeSum.LightScales

open Light ThreeSum.Scales

variable {lim : Limits} {P : Program}




theorem root_le_self (m : ℕ) : Nat.nthRoot 3 m ≤ m :=
  (Nat.le_self_pow (by decide : 3 ≠ 0) (Nat.nthRoot 3 m)).trans
    (Nat.pow_nthRoot_le (Or.inl (by decide : 3 ≠ 0)))




theorem microHalf_le_self (m : ℕ) : microHalf m ≤ m :=
  (Nat.div_le_self (Nat.nthRoot 3 m) 2).trans (root_le_self m)

theorem blockCount_le (m : ℕ) : blockCount m ≤ 20*m :=
  Nat.mul_le_mul_left 20 (Nat.div_le_self m (100*microSize m))

theorem totalSize_le_self (m : ℕ) : totalSize m ≤ m := by
  have h := totalSize_upper m
  omega






























































































































































end ThreeSum.LightScales

end

section


/-! # Concrete source inputs from the retained normalization and wanted outputs -/

namespace ThreeSum.SourceFiniteInputs

open Light GlobalEncoding LocalCoverBounds LightLocalCoverLayout LightLocalCoverSchedule

































theorem prepared_bound {μ : ℕ → ℤ} {values endpoints g U : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (H : LightBandPreprocessing.Represents μ values endpoints g hg original L hs)
    (hb : ∀ z ∈ original, |z| ≤ (U : ℤ)) :
    ∀ j < L.length, |L.getD j 0| ≤ (U : ℤ) := by
  intro j hj
  rw [List.getD_eq_getElem _ _ hj]
  exact hb _ ((H.2.2.1 _).mp (List.getElem_mem hj))


















end ThreeSum.SourceFiniteInputs

end

section


/-! # Finite charge of the actual original-band histogram and bucket catalog -/

namespace ThreeSum.SourceBandCosts

open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds

theorem choose_mul_le (L K N M : ℕ) : L.choose K*N.choose M ≤ (L+N).choose (K+M) := by
  rw [Nat.add_choose_eq]
  exact Finset.single_le_sum (f := fun ij : ℕ×ℕ => L.choose ij.1*N.choose ij.2)
    (fun _ _ => Nat.zero_le _) (by simp : (K,M) ∈ Finset.antidiagonal (K+M))

theorem choose_pow_le (L K J : ℕ) : (L.choose K)^J ≤ (J*L).choose (J*K) := by
  induction J with
  | zero => simp
  | succ J ih =>
    calc
      _ = (L.choose K)^J*L.choose K := pow_succ _ _
      _ ≤ (J*L).choose (J*K)*L.choose K := Nat.mul_le_mul_right _ ih
      _ ≤ (J*L+L).choose (J*K+K) := choose_mul_le _ _ _ _
      _ = _ := by simp only [Nat.succ_mul]

theorem typedOutputs_le_fullOutputs (n : ℕ) : typedOutputs n ≤ fullOutputs n := by
  have h := choose_pow_le (256*muZero n) (muZero n) (blockCount (inputBits n))
  have hwidth : blockCount (inputBits n)*(256*muZero n)=256*mu n := by
    unfold mu muZero totalSize
    ring
  have hcut : blockCount (inputBits n)*muZero n=mu n := rfl
  rw [hwidth,hcut] at h
  exact h





































theorem bandSize_le_fullOutputs (n : ℕ) : bandSize n ≤ fullOutputs n := by
  have hb : bandSize n ≤ bandRoot n := by
    apply (ceilDiv_le_iff_le_mul (a := bandDivisor n) (bandDivisor_pos n)).mpr
    exact Nat.le_mul_of_pos_left _ (bandDivisor_pos n)
  have hr : bandRoot n ≤ typedOutputs n := by
    have hs := Nat.sqrt_le_self (typedOutputs n-1)
    have hp := typedOutputs_pos n
    unfold bandRoot rootCeiling
    omega
  exact hb.trans (hr.trans (typedOutputs_le_fullOutputs n))

































theorem size_le_bandCount {N n : ℕ} (hN : N ≤ n) : BandPartition.size N (bandSize n) ≤ bandCount n := by
  apply (BandPartition.size_mono hN).trans
  by_cases hn : n=0
  · simp [hn,BandPartition.size]
  · have hg := bandSize_pos n
    have hb := (bandCount_mul_bounds n).1
    have hb' : n ≤ bandCount n*bandSize n := by simpa only [Nat.mul_comm] using hb
    have hd : (n-1)/bandSize n < bandCount n :=
      (Nat.div_lt_iff_lt_mul hg).mpr (by omega)
    simp only [BandPartition.size,if_neg hn]
    omega































end ThreeSum.SourceBandCosts

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






































theorem moduli_pos {A B C : List ℤ} {g y : ℕ} {hg : 0 < g}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hy : 0 < y) (i : ℕ) : 0 < LightEncodedColorPrime.moduli A B C g hg hsA hsB hsC y i :=
  BandPrimeChoice.modulus_pos (LightPrimePool.prime y)
    (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
    (BandRawA.sortedRecords A B C g hg hsA hsB hsC) (LightPrimePool.size_pos hy)
    (fun j hj => (LightPrimePool.prime_spec hj).1) i

theorem scheduled_modulus_eq (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    LightEncodedColorPrime.moduli A B C (bandSize n) (bandSize_pos n) hsA hsB hsC (primeWindow n)
      (LightBandPrimeDepth.depth (radix n) (primeWindow n))=
      BandPrimeScales.modulus n A.length B.length C.length
        (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
        (BandRawA.sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC) := rfl

theorem scheduled_modulus_guard {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hR : 4 ≤ radix n) :
    4*LightEncodedColorPrime.moduli A B C (bandSize n) (bandSize_pos n) hsA hsB hsC (primeWindow n)
      (LightBandPrimeDepth.depth (radix n) (primeWindow n)) ≤ radix n := by
  rw [scheduled_modulus_eq]
  exact BandPrimeScales.modulus_guard _ _ _ _ hR

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






























end ThreeSum.EncodedColorNormalizedData

end

section


/-! # The same normalized finite witnesses and their actually selected prime -/

namespace ThreeSum.EncodedColorPrimeReadyData

open Light Scales BandScales ColorClassLists EncodedColorLayout EncodedColorNormalizedData





















theorem selected_pos {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)} :
    0 < selected n A B C hsA hsB hsC :=
  EncodedColorPrimeCosts.moduli_pos (lt_of_lt_of_le (by decide : 0 < 2) (primeWindow_ge_two n)) _

theorem selected_guard {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hR : 4 ≤ radix n) : 4*selected n A B C hsA hsB hsC ≤ radix n :=
  EncodedColorPrimeCosts.scheduled_modulus_guard hR

end ThreeSum.EncodedColorPrimeReadyData

end

section


/-!
# Construct the dense-stop threshold from actual cover and source records

The host computes the representation cap, recomputes the exact aggregate
weighted score at the selected common modulus, multiplies the two, and
initializes the running counter. The four retained cells are counter,
threshold, representation cap and weighted score. Scratch starts after them.
-/

namespace ThreeSum.LightDenseSetup

open Light GlobalEncoding BandCandidateRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000




































theorem falseScore_eq (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) :
    falseScore primes s q nA nB nC g A B C rs=
      BandWeightedScore.score primes s q nA nB nC g A B C rs :=
  BandRawA.finiteAll_weightedFalseCount primes s q nA nB nC g A B C rs

variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs q aux s cover free maxMod U h J : ℕ}




























































































end ThreeSum.LightDenseSetup

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












theorem representation_cap_eq (n : ℕ) :
    representationCap (microHalf (inputBits n)) (blockCount (inputBits n))=
      TrimScales.representationBound n := by
  unfold representationCap TrimScales.representationBound TrimScales.localLength
  rw [scheduleSize_eq_length]

variable {μ : ℕ → ℤ} {free n : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n → ℤ}
    {A B C : List ℤ} {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

theorem normalized_lengths (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    A.length ≤ n ∧ B.length ≤ n ∧ C.length ≤ n :=
  ⟨H.normalized.2.1.2.1.trans (length_classList_le color x 0 1),
    H.normalized.2.2.1.2.1.trans (length_classList_le color x 1 1),
    H.normalized.2.2.2.1.2.1.trans (length_classList_le color x 2 (-1))⟩

theorem normalized_values {U : ℕ}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    (∀ j < A.length, |A.getD j 0| ≤ (U : ℤ)) ∧
      (∀ j < B.length, |B.getD j 0| ≤ (U : ℤ)) ∧
      (∀ j < C.length, |C.getD j 0| ≤ (U : ℤ)) :=
  ⟨SourceFiniteInputs.prepared_bound H.normalized.2.1
      (LightColorBands.class_bounded color x 0 1 (by norm_num) hx),
    SourceFiniteInputs.prepared_bound H.normalized.2.2.1
      (LightColorBands.class_bounded color x 1 1 (by norm_num) hx),
    SourceFiniteInputs.prepared_bound H.normalized.2.2.2.1
      (LightColorBands.class_bounded color x 2 (-1) (by norm_num) hx)⟩

theorem records_length_le (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    (BandRawA.sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC).length ≤ 3*bandCount n^2 := by
  obtain ⟨ha,hb,hc⟩ := normalized_lengths H
  have hr := EncodedColorNormalizedData.records_length_le ha hb hc
    (g := bandSize n) (hg := bandSize_pos n) (hsA := hsA) (hsB := hsB) (hsC := hsC)
  have hs := SourceBandCosts.size_le_bandCount (n := n) (le_refl n)
  exact hr.trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hs 2))

































theorem false_score_eq (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    falseScore n A B C hsA hsB hsC=
      BandPrimeScales.score n (BandPrimeScales.modulus n A.length B.length C.length
        (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
        (BandRawA.sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC))
        A.length B.length C.length (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
        (BandRawA.sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC) := by
  unfold falseScore
  rw [LightDenseSetup.falseScore_eq]
  rfl

theorem false_score_le_budget {k : ℕ}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hbudget : divisorBudget k n*primeWindow n ≤ candidateCount n*(4*(k+2)*(inputBits n+1)))
    (hx : ∀ i, |x i| ≤ ((n^k : ℕ) : ℤ)) :
    falseScore n A B C hsA hsB hsC ≤ UniformStageBounds.falseBudget k n := by
  obtain ⟨ha,hb,hc⟩ := normalized_values H hx
  have ha' : ∀ j < A.length, |A.getD j 0| ≤ (n^k : ℤ) := by simpa only [Nat.cast_pow] using ha
  have hb' : ∀ j < B.length, |B.getD j 0| ≤ (n^k : ℤ) := by simpa only [Nat.cast_pow] using hb
  have hc' : ∀ j < C.length, |C.getD j 0| ≤ (n^k : ℤ) := by simpa only [Nat.cast_pow] using hc
  rw [false_score_eq]
  exact UniformStageBounds.false_le_budget
    (BandPrimeScales.score_loss _ _ _ _ hbudget ha' hb' hc')
    (BandPrimeScales.initial_score_bound _ _ _ _ (records_length_le H))
    (BandPrimeScales.modulus_loss n _ _ _ _ _ _ _)

theorem threshold_le_budget {k : ℕ}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hbudget : divisorBudget k n*primeWindow n ≤ candidateCount n*(4*(k+2)*(inputBits n+1)))
    (hx : ∀ i, |x i| ≤ ((n^k : ℕ) : ℤ)) :
    representationCap (microHalf (inputBits n)) (blockCount (inputBits n))*falseScore n A B C hsA hsB hsC ≤
      UniformStageBounds.falseBudget k n*TrimScales.representationBound n := by
  rw [representation_cap_eq,Nat.mul_comm]
  exact Nat.mul_le_mul_right _ (false_score_le_budget H hbudget hx)

open Filter













end ThreeSum.ThreeSumColorBudgets

end

section


/-! # Exact level layout and retention for one shared source pair -/

namespace ThreeSum.SharedReportingBankLevels

open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData

set_option maxHeartbeats 1400000













theorem level_le {J k : ℕ} (hk : k ≤ LightSwitchDepth.depth J) : k ≤ J := by
  have hh := Nat.div_mul_le_self (13*J) 20
  unfold LightSwitchDepth.depth at hk
  omega











































































































end ThreeSum.SharedReportingBankLevels

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


/-!
# Explicit finite resource envelopes for the executed shared reporting bank

The envelopes below include the entire header and metadata slab, every
compact payload and construction scratch region, all prefix/local counts,
packed keys, switch intermediates, and both independent source lengths.
They are derived from the actual finite host contract.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light SubsetAddress SharedReportingBankLayout SharedReportingBankLevels
open SharedReportingBankHeader SharedReportingBankRows

set_option maxHeartbeats 2800000
set_option maxRecDepth 14000





















































































theorem total_le {NB NC n h J g : ℕ} (hB : NB ≤ n) (hC : NC ≤ n) :
    total h J NB NC g ≤ LightBlockSourceCatalog.count h J*n*n :=
  Nat.mul_le_mul (Nat.mul_le_mul_left _ ((BandPartition.size_le NB g).trans hB))
    ((BandPartition.size_le NC g).trans hC)

theorem space_le {free h J NB NC g n : ℕ} (hB : NB ≤ n) (hC : NC ≤ n) :
    LightSharedReportingHost.space free h J NB NC g ≤ free+extent h J n := by
  have hP := total_le (h := h) (J := J) (g := g) hB hC
  have ho := offset_le h J
  have hm := Nat.mul_le_mul_left (total h J NB NC g) ho
  have hp := Nat.mul_le_mul_right (5*levels J+levels J*cellBound h J) hP
  unfold LightSharedReportingHost.space
  apply max_le
  · unfold records LightPascal.tableSize extent
    omega
  · unfold SharedReportingBankHeader.finish rowBase payload records extent
    nlinarith



















































































end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # Finite scale bounds for every shared-bank resource component -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales Light SubsetAddress SharedReportingBankLayout SharedReportingBankHeader

set_option maxHeartbeats 3000000
set_option maxRecDepth 14000




























theorem primitive_bounds (n : ℕ) :
    _root_.ThreeSum.SharedReportingBankResourceBounds.half n ≤ inputBits n ∧ _root_.ThreeSum.SharedReportingBankResourceBounds.blocks n ≤ 20*inputBits n ∧
    2*_root_.ThreeSum.SharedReportingBankResourceBounds.half n*_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n ≤ inputBits n ∧
    width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n) ≤ 256*inputBits n := by
  have hh := LightScales.microHalf_le_self (inputBits n)
  have hj := LightScales.blockCount_le (inputBits n)
  have ht := LightScales.totalSize_le_self (inputBits n)
  change _root_.ThreeSum.SharedReportingBankResourceBounds.blocks n*(2*_root_.ThreeSum.SharedReportingBankResourceBounds.half n) ≤ inputBits n at ht
  refine ⟨hh,hj,by nlinarith,?_⟩
  unfold width localWidth
  nlinarith
















































theorem band_le_magnitude (n : ℕ) : BandScales.bandSize n ≤ magnitude n := by
  have hB := SourceBandCosts.bandSize_le_fullOutputs n
  have hfull : TrimScales.fullOutputs n ≤ 2^(width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n)) := by
    rw [show width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n)=256*mu n from BlockSourceSharing.width_eq n]
    exact Nat.choose_le_two_pow _ _
  exact (hB.trans hfull).trans ((Nat.pow_le_pow_right (by decide) (by omega : width (half n) (blocks n) ≤
    width (half n) (blocks n)+1)).trans (components n).widthPower)


























































































































































































end ThreeSum.SharedReportingBankResourceBounds

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






















end ThreeSum.ThreeSumReportingSetupData

end

section


/-!
# Exact resource formulas for the original-input band and incidence program

These formulas use the existing selected-color layout without changing any
address or procedure. The physical BC, AB, AC owner records and the packed
value, owner, and sorted-position arrays are all included in the extent.
-/

namespace ThreeSum.LightBandRawAResources

open Light EncodedColorLayout

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000






















theorem count_le (n g : ℕ) : ColorBandBounds.count n g ≤ 3*n^2 :=
  Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (BandPartition.size_le n g) 2)






















end ThreeSum.LightBandRawAResources

end

section


/-!
# The original source header after shared reporting and dense initialization

The prelude returns the source header unchanged. The reporting header starts
eight cells later, and its field six contains the initialized dense counter.
All contracts retain the same normalized A, B and C witnesses.
-/

namespace ThreeSum.EncodedColorReportingData

open Light Scales BandScales EncodedColorNormalizedData ThreeSumReportingSetupData

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

local instance (n : ℕ) : NeZero (radix n) := ⟨Nat.ne_of_gt (radix_pos n)⟩















theorem counter_read {μ : ℕ → ℤ} {free n : ℕ} {color : Coloring.Parameter (inputBits n+1)}
    {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC) :
    μ (EncodedColorPipelineData.finish free n A B C hsA hsB hsC+14)=
      (counter free n A B C hsA hsB hsC : ℤ) := by
  have hh := H.catalog.heads 6 (by simp [SharedReportingBankHeader.header])
  simpa [SharedReportingBankHeader.header,reportBase,counter,Nat.add_assoc] using hh







































end ThreeSum.EncodedColorReportingData

end

section


/-!
# Size-only magnitudes for physical wanted indices

The left index includes the lift and the retained A-incidence position.
The right index selects an original output record, including its occurrence
identity. Neither bound depends on the magnitude of the input integers.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales GlobalEncoding LocalCoverBounds OutputDecodeRecords
open SharedReportingBankLayout

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000



theorem input_le_magnitude (n : ℕ) : n ≤ magnitude n := by
  have hn : n ≤ 2^(inputBits n+1) := by
    simpa only [inputBits,Nat.log2_eq_log_two,Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by decide : 1<2) n).le
  exact hn.trans (Nat.pow_le_pow_right (by decide) (by omega))







theorem local_layer_le_magnitude (n : ℕ) : layerCount (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) ≤ magnitude n := by
  have hc : layerCount (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) ≤ 2^(512*_root_.ThreeSum.SharedReportingBankResourceBounds.half n) := Nat.choose_le_two_pow _ _
  exact hc.trans ((Nat.pow_le_pow_right (by decide) (by omega)).trans (components n).localPower)

theorem local_schedule_le_magnitude (n : ℕ) : scheduleSize (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) ≤ magnitude n := by
  have hh := (primitive_bounds n).1
  exact (LightLocalCoverMagnitude.rounds_bound (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)).trans
    (Nat.pow_le_pow_right (by decide) (by omega))













































































end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # Explicit finite scale bounds for reporter words and the dense counter -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales Light GlobalEncoding LocalCoverBounds SharedReportingBankLayout
open ReportingHostWantedLayout

set_option maxHeartbeats 2800000
set_option maxRecDepth 14000
























theorem wanted_modulus_le_magnitude (n : ℕ) :
    BlockSourceEncoding.modulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n)≤magnitude n := by
  have hp := (components n).primePower
  exact (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero
    (LocalCoverBounds.localPrime_prime (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)).ne_zero)).trans hp








































































































end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # Compose the two actual reporting allocations at an arbitrary free pointer -/

namespace ThreeSum.ThreeSumReportingSetupResources

open Light Scales BandScales ThreeSumReportingSetupData

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000






theorem counter_le {μ : ℕ → ℤ} {free n : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) (U : ℕ) :
    counter free n A B C hsA hsB hsC ≤ reportBase free n A B C hsA hsB hsC+
      (SharedReportingBankResourceBounds.need n U).cells := by
  obtain ⟨_,hB,hC⟩ := ThreeSumColorBudgets.normalized_lengths H
  exact (le_max_right _ _).trans (SharedReportingBankResourceBounds.space_le
    (free := reportBase free n A B C hsA hsB hsC) (h := microHalf (inputBits n))
    (J := blockCount (inputBits n)) (g := bandSize n) hB hC)












noncomputable section























end
end ThreeSum.ThreeSumReportingSetupResources

end

section


/-! # Affine resources for source construction followed by reporting setup -/

namespace ThreeSum.EncodedColorReportingResources

open Light Scales BandScales ThreeSumReportingSetupData

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
















theorem counter_end_le_allocation {μ : ℕ → ℤ} {free n : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : 0 < n) (U : ℕ) :
    counter free n A B C hsA hsB hsC+4 ≤ free+(need n U).cells := by
  have hr := EncodedColorReportingData.report_le_source_allocation H hn U
  have hc := ThreeSumReportingSetupResources.counter_le H U
  have hd : 4 ≤ (SharedReportingBankResourceBounds.denseNeed n U).cells := by
    change 4 ≤ SharedReportingBankResourceBounds.denseCells n U
    unfold SharedReportingBankResourceBounds.denseCells
    omega
  dsimp only [need,ThreeSumReportingSetupResources.need]
  omega

noncomputable section























end
end ThreeSum.EncodedColorReportingResources

end

section


/-!
# The actual wanted array on physical owner-incidence indices

The key constructor uses the mapped A-value list. The reporter and dense
owner domains use physical positions in the incidence-label list. Their
length-preserving transport keeps every physical position, lift and full
output record, including positions holding equal integer values.
-/

namespace ThreeSum.ReportingHostWantedPhysical

open Light BandRawA BandCandidateRows RawIncidences GlobalEncoding

set_option maxHeartbeats 2100000
set_option maxRecDepth 10000
































section Actual

variable {μ : ℕ→ℤ} {f : ℕ→ℤ} {n g free M P h J : ℕ}
  {rs : List Record} {shift : ℤ}
  (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P (values f (items n g rs)))
    (LightGuardedWanted.right h J) (3*(values f (items n g rs)).length)
    (LightGuardedWanted.totalKeys h J) shift)


































theorem wantedAt_key (slot : Fin (μ free).toNat) :
    (M : ℤ) ∣ valueAt n g rs f (wantedAt H slot).1.val%(P : ℤ)+
      lift (wantedAt H slot).2.1*(P : ℤ)+shift-globalKey (wantedAt H slot).2.2 := by
  exact RawAKeyLists.mem_wanted.mp (DenseGuardWanted.labelAt_mem H slot)

































end Actual

end ThreeSum.ReportingHostWantedPhysical

end

section


/-!
# Actual emitted slots decide the complete physical owner domain

Each slot selects its own independently retained B/C bands. Its terminal
semantics is the exact finite owner fiber, while the cumulative guard uses
their disjoint global union. This connects the physical wanted array to
original-value terminal tests at every permitted partial reporting depth.
-/

namespace ThreeSum.ReportingHostWantedOriginal

open Finset Light BandRawA BandCandidateRows RawIncidences RawReporting
open GlobalEncoding ReportingHostWantedPhysical
open ReportingHostFrontierLayout

set_option maxHeartbeats 2300000
set_option maxRecDepth 12000





































theorem owner_lt {h J n g : ℕ} (rs : List Record) (w : Wanted h J (AType n g rs)) :
    owner rs w<rs.length := (at_bounds w.1.isLt).1











theorem global_local_mass {h J n NB NC g p : ℕ} (rs : List Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : Wanted h J (AType n g rs)) :
    rootMass (globalItems h J n NB NC g p rs fA fB fC shift) w=
      rootMass (localItems h J n NB NC g p rs fA fB fC shift w) w :=
  DenseGuardBands.rootMass_global_eq_owner rs (owner_lt rs w) _ _ _ w rfl














































section Actual

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n NB NC g free P h J : ℕ}
  {rs : List Record} {shift : ℤ}
  (H : LightWantedSetup.Output μ free (LocalCoverBounds.localPrime h^J)
    (LightGuardedWanted.left P (values fA (items n g rs))) (LightGuardedWanted.right h J)
    (3*(values fA (items n g rs)).length) (LightGuardedWanted.totalKeys h J) shift)
























end Actual

end ThreeSum.ReportingHostWantedOriginal

end

section


/-!
# The exact dense counter of the physical ascending wanted scan

The finite physical labels are injective even when input values repeat.
The sum of the queried owner masses in any prefix is consequently the
mass of a distinct-label prefix in the complete original domain.
-/

namespace ThreeSum.ReportingHostWantedPrefix

open Finset Light BandRawA BandCandidateRows RawIncidences RawReporting
open GlobalEncoding ReportingHostWantedPhysical ReportingHostWantedOriginal
open ReportingHostFrontierLayout SharedTraversalCosts

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

section Actual

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n NB NC g free P h J : ℕ}
  {rs : List Record} {shift : ℤ}
  (H : LightWantedSetup.Output μ free (LocalCoverBounds.localPrime h^J)
    (LightGuardedWanted.left P (values fA (items n g rs))) (LightGuardedWanted.right h J)
    (3*(values fA (items n g rs)).length) (LightGuardedWanted.totalKeys h J) shift)




















theorem slotMass_at (fB fC : ℕ→ℤ) (NB NC : ℕ) (i : Fin (μ free).toNat) :
    slotMass H fB fC NB NC i.val=
      rootMass (globalItems h J n NB NC g P rs fA fB fC shift) (wantedAt H i) := by
  simp only [slotMass,dif_pos i.isLt]
  exact (global_local_mass rs fA fB fC shift (wantedAt H i)).symm


































end Actual

end ThreeSum.ReportingHostWantedPrefix

end

section


/-!
# The actual retained inputs of the physical wanted consumer

These are projections and finite bounds for the same normalized witnesses
retained by the selected-color pipeline. Physical A incidences preserve
their owner labels even when their integer values are equal.
-/

namespace ThreeSum.EncodedColorWantedConsumerData

open Light Scales BandScales EncodedColorNormalizedData ThreeSumWantedHostData

set_option maxHeartbeats 2200000
set_option maxRecDepth 16000















variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}









































theorem record_count_le (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    recordCount n A B C hsA hsB hsC≤ColorBandBounds.count n (bandSize n) := by
  obtain ⟨ha,hb,hc⟩ := ThreeSumColorBudgets.normalized_lengths H
  exact EncodedColorNormalizedData.records_length_le ha hb hc
















































end ThreeSum.EncodedColorWantedConsumerData

end

section


/-!
# Retain the selected-color inputs while the wanted counter changes

Only the first dense-header cell is mutable during the scan. The encoded
payload, shared reporting catalog, threshold, cap and original false score
remain available with exactly the same normalized-list witnesses.
-/

namespace ThreeSum.EncodedColorWantedConsumerData

open Light Scales BandScales ThreeSumWantedHostData

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000





variable {μ ν : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

theorem kept_counter
    (K : KeptBut μ ν (config free n A B C hsA hsB hsC).layoutHeader
      (config free n A B C hsA hsB hsC).counter 1) :
    Kept μ ν (config free n A B C hsA hsB hsC).counter := by
  intro a ha
  have he : (config free n A B C hsA hsB hsC).layoutHeader=
      (config free n A B C hsA hsB hsC).counter+4 := rfl
  exact K a ⟨by omega,Or.inl ha⟩
















































end ThreeSum.EncodedColorWantedConsumerData

end

section


/-! # Polynomial relative resources for every physical wanted slot -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Scales StageBounds GlobalEncoding LocalCoverBounds
open SharedReportingBankLayout ReportingHostWantedLayout

set_option maxHeartbeats 3200000
set_option maxRecDepth 16000






theorem wanted_power_le (n e f : ℕ) (hef : e≤f) :
    (magnitude n)^e≤(magnitude n+1)^f :=
  (Nat.pow_le_pow_left (Nat.le_succ _) e).trans (Nat.pow_le_pow_right (by omega) hef)











































































































































noncomputable section









































end
end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # Physical labels and original-fiber semantics for the retained consumer -/

namespace ThreeSum.ReportingHostWantedConsumerData

open Light Scales BandScales BandRawA RawReporting RawIncidences GlobalEncoding
open EncodedColorNormalizedData EncodedColorWantedConsumerData ThreeSumWantedHostData
open ReportingHostWantedOriginal ReportingHostWantedPhysical SharedReportingBankResourceBounds
open ReportingHostFrontierLayout

set_option maxHeartbeats 2300000
set_option maxRecDepth 16000





















































variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}














































theorem label_key (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC)) :
    globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n) ∣
      valueAt A.length (bandSize n) (records n A B C hsA hsB hsC) (fun j => A.getD j 0) (label H s).1.val %
        (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)+
      lift (label H s).2.1*(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)+
      ThreeSumReportingSetupData.shift n A B C hsA hsB hsC-globalKey (label H s).2.2 := by
  have hm : globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n)=(radix n : ℤ) := by
    simp only [globalModulus,Scales.radix,Scales.localRadix,Nat.cast_pow,_root_.ThreeSum.SharedReportingBankResourceBounds.half,_root_.ThreeSum.SharedReportingBankResourceBounds.blocks]
  rw [hm]
  exact wantedAt_key H.wanted (slot H s)

end ThreeSum.ReportingHostWantedConsumerData

end

section


/-! # Frozen physical order and the exact cost of the ascending consumer -/

namespace ThreeSum.ReportingHostWantedConsumerData

open Light Scales BandScales BandRawA RawReporting RawIncidences GlobalEncoding
open EncodedColorNormalizedData EncodedColorWantedConsumerData ThreeSumWantedHostData
open SharedReportingBankResourceBounds SharedTraversalCosts

set_option maxHeartbeats 2200000
set_option maxRecDepth 17000





variable {μ ν : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}



















theorem mass_at (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC)) :
    mass H s.val=labelMass n A B C hsA hsB hsC (label H s) := by
  exact (ReportingHostWantedPrefix.slotMass_at H.wanted
    (fun j => B.getD j 0) (fun j => C.getD j 0) B.length C.length (slot H s)).trans
      (ReportingHostWantedOriginal.global_local_mass (records n A B C hsA hsB hsC)
        (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
        (ThreeSumReportingSetupData.shift n A B C hsA hsB hsC) (label H s))








theorem stepTime_at (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC)) :
    stepTime H s.val=
      LightReportingWantedDispatch.time (config free n A B C hsA hsB hsC) (wantedDecodeV n)
        (recordTime free n A B C hsA hsB hsC (label H s)
          (outputIndex μ (config free n A B C hsA hsB hsC) s.val)
          (prefixMass (mass H) s.val) (threshold n A B C hsA hsB hsC)) := by
  simp only [stepTime,dif_pos s.isLt]




































end ThreeSum.ReportingHostWantedConsumerData

end

section


/-! # Physical mass limits from the retained selected color

The positive common modulus, its guard, every physical incidence count,
and both original sorted-source lengths come from the executed pipeline.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Scales BandScales BandRawA RawReporting GlobalEncoding
open ReportingHostFrontierLayout ReportingHostWantedOriginal
open EncodedColorNormalizedData EncodedColorWantedConsumerData

set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}











theorem wanted_selected_guard (hR : 4≤radix n) :
    4*(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)≤globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n) := by
  have hh : 4*(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)≤(radix n : ℤ) := by
    exact_mod_cast EncodedColorPrimeReadyData.selected_guard (A := A) (B := B) (C := C)
      (hsA := hsA) (hsB := hsB) (hsC := hsC) hR
  simpa only [globalModulus,Scales.radix,Scales.localRadix,_root_.ThreeSum.SharedReportingBankResourceBounds.half,_root_.ThreeSum.SharedReportingBankResourceBounds.blocks,Nat.cast_pow] using hh




































theorem wanted_stored_threshold_le
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    representationCap (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n)*ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC≤
      9*(magnitude n)^8 := by
  have hrs : (records n A B C hsA hsB hsC).length≤3*n^2 :=
    (record_count_le H).trans
      (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (BandPartition.size_le n (bandSize n)) 2))
  exact wanted_threshold_le (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
    (records n A B C hsA hsB hsC) hrs






















end ThreeSum.SharedReportingBankResourceBounds

end

section


/-!
# Execute the complete original physical wanted array

The invariant preserves the initial physical wanted order, all original
source data and all fixed dense metadata. The mutable counter is exactly
the mass of the ascending executed prefix until the first successful call.
-/

namespace ThreeSum.LightReportingWantedScanStored

open Light Scales BandScales BandRawA RawReporting RawIncidences GlobalEncoding
open EncodedColorNormalizedData EncodedColorWantedConsumerData ThreeSumWantedHostData
open ReportingHostWantedConsumerData SharedReportingBankResourceBounds SharedTraversalCosts

set_option maxHeartbeats 3200000
set_option maxRecDepth 22000
set_option linter.unusedSectionVars false













































































/-- At the actual schedule the selected modulus, complete prefix magnitudes
and dense threshold need no input-dependent numeric assumptions. -/
theorem program_meets_of_radix {lim : Limits} {μ : ℕ→ℤ} {free n U d : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (hx : ∀ i, |x i|≤(U : ℤ)) (hR : 4≤radix n)
    (hok : (wantedScanNeed n U).Ok lim (config free n A B C hsA hsB hsC).layoutHeader d) :
    Meets lim LightReportingWantedScan.program 152 d
      (LightReportingWantedDispatch.arguments (config free n A B C hsA hsB hsC)
        (count n A B C hsA hsB hsC)) μ (scanTime H.encoded)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ LightReportingWantedScan.Accepted (mass H.encoded) (hit H.encoded)
          (threshold n A B C hsA hsB hsC) (count n A B C hsA hsB hsC)) ∧
        LightReportingWantedScan.Counter (mass H.encoded) (hit H.encoded)
          (threshold n A B C hsA hsB hsC) (count n A B C hsA hsB hsC)
          (config free n A B C hsA hsB hsC).counter r ν ∧
        KeptBut μ ν (config free n A B C hsA hsB hsC).layoutHeader
          (config free n A B C hsA hsB hsC).counter 1) :=
  program_meets H hx EncodedColorPrimeReadyData.selected_pos (wanted_selected_guard hR)
    (wanted_stored_threshold_le H.encoded) hok

end ThreeSum.LightReportingWantedScanStored

end

section


/-! # Relative limits for the complete wanted-header loader and scan

All numeric controls come from the input size. The loader starts its reusable
scratch at `counter+4`; every retained absolute pointer is handled by its
individual allocation end rather than being included in a numeric envelope.
-/

namespace ThreeSum.ThreeSumFastResources

open Light Scales BandScales StageBounds SharedReportingBankResourceBounds

set_option maxHeartbeats 2100000
set_option maxRecDepth 15000










theorem terminal_depth_le (n : ℕ) : LightSwitchDepth.depth (_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n)≤_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n :=
  SharedReportingBankLevels.level_le le_rfl

theorem record_cap_le (n : ℕ) : ColorBandBounds.count n (bandSize n)≤3*(magnitude n)^2 :=
  (LightBandRawAResources.count_le n (bandSize n)).trans
    (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (input_le_magnitude n) 2))

theorem incidence_cap_le (n : ℕ) : EncodedColorStageCosts.incidenceCap n≤3*(magnitude n)^3 := by
  have hh := Nat.mul_le_mul (band_le_magnitude n) (record_cap_le n)
  unfold EncodedColorStageCosts.incidenceCap
  calc
    _ ≤ magnitude n*(3*(magnitude n)^2) := hh
    _ = _ := by ring

theorem radix_le (n : ℕ) : radix n≤magnitude n := wanted_modulus_le_magnitude n

theorem header_word_le (n : ℕ) : headerWord n≤wantedEnvelope n := by
  have hn := input_le_magnitude n
  have hJ := (components n).blocksBound
  have hL := (components n).localWidthBound
  have hK := terminal_depth_le n
  have hg := band_le_magnitude n
  have hr := radix_le n
  have hl := local_layer_le_magnitude n
  have hs : GlobalEncoding.scheduleSize (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)≤magnitude n := local_schedule_le_magnitude n
  have hR := record_cap_le n
  have hN := incidence_cap_le n
  have h2 := wanted_power_le n 2 10 (by decide)
  have h3 := wanted_power_le n 3 10 (by decide)
  have hM : magnitude n≤(magnitude n+1)^10 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  have h1 : 1≤(magnitude n+1)^10 := Nat.one_le_pow _ _ (by omega)
  unfold headerWord wantedEnvelope
  omega

theorem header_slack_le (n : ℕ) : 50+2*_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n≤wantedEnvelope n := by
  have hJ := (components n).blocksBound
  have hM : magnitude n≤(magnitude n+1)^10 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  have h1 : 1≤(magnitude n+1)^10 := Nat.one_le_pow _ _ (by omega)
  unfold wantedEnvelope
  omega

theorem scan_of_ok {lim : Limits} {n U dst d : ℕ} (hok : (need n U).Ok lim dst d) :
    (wantedScanNeed n U).Ok lim dst (d+1) :=
  hok.mono le_rfl le_rfl (by dsimp only [need]; omega)






theorem header_space_of_ok {lim : Limits} {n U counter d : ℕ}
    (hok : (need n U).Ok lim (counter+4) d) : counter+50+2*_root_.ThreeSum.SharedReportingBankResourceBounds.blocks n≤lim.space := by
  have hc := hok.cells
  change counter+4+wantedEnvelope n≤lim.space at hc
  have hh := header_slack_le n
  omega

theorem header_word_of_ok {lim : Limits} {n U dst d : ℕ}
    (hok : (need n U).Ok lim dst d) : (headerWord n : ℤ)≤lim.word := by
  have hh := (header_word_le n).trans (Nat.le_mul_of_pos_right _ (by omega : 0<U+1))
  exact (Int.ofNat_le.mpr hh).trans hok.word

theorem outer_depth_of_ok {lim : Limits} {n U dst d : ℕ}
    (hok : (need n U).Ok lim dst d) : d<lim.depth := by
  have hh := hok.depth
  change d+((wantedNeed n U).depth+wantedScanCount n+4+2)≤lim.depth at hh
  omega

noncomputable section



















end
end ThreeSum.ThreeSumFastResources

end

section


/-! # One affine allocation for a complete selected color

The prelude retains its source and reporting catalogs, ending with the dense
counter. The wanted scan reuses scratch beginning four cells after that
counter. The two exact resource records are combined without bounding the
absolute starting address.
-/

namespace ThreeSum.ThreeSumFastResourcesColor

open Light Scales BandScales ThreeSumReportingSetupData

set_option maxHeartbeats 1800000
set_option maxRecDepth 15000






theorem prelude_of_ok {lim : Limits} {free n U d : ℕ}
    (H : (need n U).Ok lim free d) :
    (EncodedColorReportingResources.need n U).Ok lim free (d+1) :=
  H.mono (by dsimp only [need]; omega) (by dsimp only [need]; omega)
    (by dsimp only [need]; omega)

theorem wanted_of_ok {lim : Limits} {free ctr n U d : ℕ}
    (H : (need n U).Ok lim free d)
    (hctr : ctr+4≤free+(EncodedColorReportingResources.need n U).cells) :
    (ThreeSumFastResources.need n U).Ok lim (ctr+4) (d+1) :=
  H.mono (by dsimp only [need]; omega) (by dsimp only [need]; omega)
    (by dsimp only [need]; omega)

theorem wanted_of_stored {lim : Limits} {μ : ℕ→ℤ} {free n U d : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : 0<n) (hok : (need n U).Ok lim free d) :
    (ThreeSumFastResources.need n U).Ok lim
      (counter free n A B C hsA hsB hsC+4) (d+1) :=
  wanted_of_ok hok (EncodedColorReportingResources.counter_end_le_allocation H.encoded hn U)

theorem scan_of_stored {lim : Limits} {μ : ℕ→ℤ} {free n U d : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : 0<n) (hok : (need n U).Ok lim free d) :
    (SharedReportingBankResourceBounds.wantedScanNeed n U).Ok lim
      (counter free n A B C hsA hsB hsC+4) (d+2) := by
  simpa only [Nat.add_assoc] using ThreeSumFastResources.scan_of_ok (wanted_of_stored H hn hok)












/-- The outer color call can load the counter at the returned source header plus14. -/
theorem counter_read_resources_of_stored {lim : Limits} {μ : ℕ→ℤ} {free n U d : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : 0<n) (hok : (need n U).Ok lim free d) :
    EncodedColorPipelineData.finish free n A B C hsA hsB hsC+15≤lim.space ∧
      counter free n A B C hsA hsB hsC+4≤lim.space := by
  have hw := wanted_of_stored H hn hok
  have hc := hw.cells
  have hp := report_le_counter free n A B C hsA hsB hsC
  unfold reportBase at hp
  omega

theorem outer_depth_of_ok {lim : Limits} {free n U d : ℕ}
    (H : (need n U).Ok lim free d) : d<lim.depth := by
  have hd := H.depth
  dsimp only [need] at hd
  omega

noncomputable section























end
end ThreeSum.ThreeSumFastResourcesColor

end

section


/-! # The actual154 wanted-header loader from its concrete Need

The executable loader and its exact scan call remain unchanged. Its
numeric controls and relative address bounds follow from the resource
record used by the complete selected-color program.
-/

namespace ThreeSum.ThreeSumFastResources

open Light Scales ThreeSumReportingSetupData ThreeSumWantedHostData

set_option maxHeartbeats 1900000
set_option maxRecDepth 17000

theorem header_word_eq (n : ℕ) : headerWord n=LightThreeSumWantedHost.word n := rfl

theorem program_meets {lim : Limits} {d T U : ℕ} {μ : ℕ→ℤ} {free n params : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    {Q : ℤ→(ℕ→ℤ)→Prop}
    (H : ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (Hparams : Seg μ params (LightParameterInit.values n)) (hparams : params+19≤free)
    (hok : (need n U).Ok lim (config free n A B C hsA hsB hsC).layoutHeader d)
    (hscan : Meets lim LightReportingWantedScan.program 152 (d+1)
      (LightReportingWantedDispatch.arguments (config free n A B C hsA hsB hsC)
        (ThreeSumWantedHostData.count n A B C hsA hsB hsC)) μ T Q) :
    Meets lim LightThreeSumWantedHost.program 153 d
      [n,params,free,EncodedColorPipelineData.finish free n A B C hsA hsB hsC,
        counter free n A B C hsA hsB hsC] μ (T+4000) Q := by
  apply LightThreeSumWantedHost.program_meets H Hparams hparams hok.space (outer_depth_of_ok hok)
    (header_space_of_ok hok) _ hscan
  simpa only [header_word_eq] using header_word_of_ok hok

theorem color_program_meets {lim : Limits} {d T U : ℕ} {μ : ℕ→ℤ} {free n params : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    {Q : ℤ→(ℕ→ℤ)→Prop}
    (H : ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (Hparams : Seg μ params (LightParameterInit.values n)) (hparams : params+19≤free)
    (hn : 0<n) (hok : (ThreeSumFastResourcesColor.need n U).Ok lim free d)
    (hscan : Meets lim LightReportingWantedScan.program 152 (d+2)
      (LightReportingWantedDispatch.arguments (config free n A B C hsA hsB hsC)
        (ThreeSumWantedHostData.count n A B C hsA hsB hsC)) μ T Q) :
    Meets lim LightThreeSumWantedHost.program 153 (d+1)
      [n,params,free,EncodedColorPipelineData.finish free n A B C hsA hsB hsC,
        counter free n A B C hsA hsB hsC] μ (T+4000) Q :=
  program_meets H Hparams hparams (ThreeSumFastResourcesColor.wanted_of_stored H hn hok) hscan

end ThreeSum.ThreeSumFastResources

end

section


/-!
# Charge the actual fixed153 wanted scan and fixed154 header caller

The concrete dispatcher contributes4500 operations, and the ascending
recursion contributes300 per slot. The exact active-branch mass remains
inside the cumulative guard until the original reporting ledger is applied.
-/

namespace ThreeSum.SharedTraversalCosts

open Light Finset Scales BandScales GlobalEncoding RawIncidences RawReporting
open ReportingHostLevelData StageBounds CostLedger
open ReportingHostFrontierLayout Parameters

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000






variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]











































/-- The time recurrence is the one proved for the actual153 executable. -/
theorem actual_scan_time_le {n k threshold count : ℕ} {mass stepTime : ℕ→ℕ}
    (hstep : ∀ i, stepTime i+300≤slotEnvelope n threshold mass i)
    (hcount : count≤UniformStageBounds.wantedBudget n)
    (hthreshold : threshold≤UniformStageBounds.falseBudget k n*TrimScales.representationBound n) :
    LightReportingWantedScan.time stepTime count≤dispatchBudget 4800 k n := by
  apply prefix_time_le_dispatch_budget (mass := mass) (threshold := threshold)
    (by rfl) _ hcount hthreshold
  intro i
  rw [LightReportingWantedScan.time]
  have hh := hstep i
  unfold slotEnvelope at hh
  omega














noncomputable section














end
end ThreeSum.SharedTraversalCosts

end

section


/-! # The exact physical scan fits the uniform selected-color budget -/

namespace ThreeSum.ThreeSumWantedHostCosts

open Light Scales BandScales BandRawA RawReporting RawIncidences GlobalEncoding
open ReportingHostWantedConsumerData SharedTraversalCosts ThreeSumWantedHostData

set_option maxHeartbeats 1800000
set_option maxRecDepth 15000

variable {μ : ℕ→ℤ} {free n k : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

theorem physical_steps_le
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) (i : ℕ) :
    stepTime H i+300≤slotEnvelope n (threshold n A B C hsA hsB hsC) (mass H) i := by
  by_cases hi : i<count n A B C hsA hsB hsC
  · have hh := physical_step_le (free := free)
      (output := outputIndex μ (config free n A B C hsA hsB hsC) i)
      (old := prefixMass (mass H) i) (threshold := threshold n A B C hsA hsB hsC)
      (label H ⟨i,hi⟩) (label_key H ⟨i,hi⟩)
    rw [stepTime_at H ⟨i,hi⟩]
    unfold slotEnvelope
    rw [mass_at H ⟨i,hi⟩]
    exact hh
  · simp only [stepTime,dif_neg hi]
    unfold slotEnvelope scalarOverhead
    omega

theorem physical_scan_time_le
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : ThreeSumWantedHostConditions.Ready k n)
    (hx : ∀ i, |x i|≤((n^k : ℕ) : ℤ)) :
    scanTime H≤dispatchBudget 4800 k n := by
  apply actual_scan_time_le (physical_steps_le H)
  · have hh := ThreeSumColorBudgets.wanted_count_le H
    rwa [count_read H,Int.toNat_natCast] at hh
  · exact ThreeSumColorBudgets.threshold_le_budget H hn.divisor hx










end ThreeSum.ThreeSumWantedHostCosts

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













theorem program_meets_sourceProof {lim : Limits} {μ : ℕ→ℤ} {src n params row free k d : ℕ}
    (color : Coloring.Parameter (inputBits n+1)) (x : Fin n→ℤ)
    (hn : Ready k n) (hsrc : src+n≤free) (hparams : params+19≤free) (hrow : row+6≤free)
    (hok : (ThreeSumFastResourcesColor.need n (n^k)).Ok lim free d)
    (hread : Seg μ src (List.ofFn x)) (hx : ∀ i, |x i|≤((n^k : ℕ) : ℤ))
    (hparameters : Seg μ params (LightParameterInit.values n))
    (hcolor : Seg μ row (ColorParameters.fields color)) :
    Meets lim program 509 d [src,n,params,row,free] μ (colorBudget k n)
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ ColorClassLists.witness color x) ∧ Kept μ ξ free) := by
  have hw := hok.space
  have hd := ThreeSumFastResourcesColor.outer_depth_of_ok hok
  apply Meets.of_body (p := 509) (by rfl : program[509]?=some (body 354 508))
  unfold body colorBudget
  have hPrelude := ((LightEncodedColorReportingPipeline.program_meets (d := d+1)
    color x hn.positive hn.radix hsrc hparams hrow
    (ThreeSumFastResourcesColor.prelude_of_ok hok) hread hx hparameters hcolor).append
      (LightThreeSumWantedHost.program.map (ReportingHostRelocation.relocate 355))).append [body 354 508]
  simp only [LightEncodedColorReportingPipeline.time] at hPrelude
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
      | refine Light.Ends.callToThen (hPrelude _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hPrelude ?_ ?_ ?_ ?_);
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
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)));
    (on_goal -1 =>
        ((rintro header ν ⟨hout, hkeepPrelude⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  obtain ⟨A,hsA,B,hsB,C,hsC,hheader,H⟩ := hout
  let sourceHeader := EncodedColorPipelineData.finish free n A B C hsA hsB hsC
  let ctr := counter free n A B C hsA hsB hsC
  have hheader' : header=(sourceHeader : ℤ) := hheader
  have hctrRead : ν (sourceHeader+14)=(ctr : ℤ) := EncodedColorReportingData.counter_read H
  obtain ⟨hsourceSpace,hctrSpace⟩ := ThreeSumFastResourcesColor.counter_read_resources_of_stored
    H hn.positive hok
  change sourceHeader+15≤lim.space at hsourceSpace
  change ctr+4≤lim.space at hctrSpace
  have hsourceWord : (sourceHeader : ℤ)+14≤lim.word := by
    have hh := (Int.ofNat_le.mpr (show sourceHeader+14≤lim.space by omega)).trans hw
    exact_mod_cast hh
  have hctrWord : (ctr : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (show ctr≤lim.space by omega)).trans hw
  have hsourceNat : ((sourceHeader : ℤ)+14).toNat=sourceHeader+14 := by omega
  focus
    ((((first
            | refine Light.Ends.seqSelf ?_
            | refine Light.Ends.skipLast ?_));
        (repeat
            with_unfolding_none
              first
              | refine Light.Ends.seqAssoc ?_
              | refine Light.Ends.skipThen ?_)));
    (refine Light.Ends.setToThen (ctr : ℕ) ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hheader', hctrRead, hsourceNat]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hheader', hctrRead, hsourceNat] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hheader', hctrRead,
                hsourceNat] <;>
              omega)));
    (try with_unfolding_none refine Light.Ends.skip ?_)
  have paramsν : Seg ν params (LightParameterInit.values n) :=
    hparameters.of_kept hkeepPrelude (by change params+19≤free; exact hparams)
  have hScan := LightReportingWantedScanStored.program_meets_of_radix H hx hn.radix
    (ThreeSumFastResourcesColor.scan_of_stored H hn.positive hok)
  have hWanted := ThreeSumFastResources.color_program_meets H paramsν hparams hn.positive hok hScan
  have hWantedTime := hWanted.mono_time
    (Nat.add_le_add_right (ThreeSumWantedHostCosts.physical_scan_time_le H.encoded hn hx) 4000)
  have hWantedCall := (ReportingHostRelocation.meets hWantedTime
    LightEncodedColorReportingPipeline.program).append [body 354 508]
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
      | refine Light.Ends.callToThen (hWantedCall _ (by omega)) ?_ ?_ ?_ ?_
      | refine Light.Ends.callToThen hWantedCall ?_ ?_ ?_ ?_);
    (on_goal -1 =>
        first
        |
          ((simp only [Light.Stmt.blockCost, Light.Cond.cost, Light.Expr.cost,
                List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                hheader', sourceHeader, ctr]);
            (first
              | omega
              | ((ring_nf); (omega))))
        | omega
        |
          (simp [hheader', sourceHeader, ctr] <;>
              first
              | omega
              | ((ring_nf); (omega))));
    (on_goal -1 => omega);
    (on_goal -1 =>
        (((try have := Light.Std.space_le (by assumption)));
          ((try have := Light.Std.const_le (by assumption)));
          (simp [Light.Limits.Addr, abs_le, -abs_mul, hheader', sourceHeader,
                ctr] <;>
              omega)));
    (on_goal -1 =>
        ((rintro result ξ ⟨hbool, hresult, _, hkeepScan⟩);
          (try with_unfolding_none refine Light.Ends.skip ?_)))
  have hwitness := ThreeSumWantedHostDecision.accepted_iff_witness H.encoded hn hx
  have hkept := EncodedColorWantedConsumerData.kept_counter hkeepScan
  have hp := (prefix_le_report free n A B C hsA hsB hsC).1
  have hc := report_le_counter free n A B C hsA hsB hsC
  exact ⟨hbool,hresult.trans hwitness,fun a ha =>
    (hkept a (by change a<counter free n A B C hsA hsB hsC; omega)).trans (hkeepPrelude a ha)⟩

end ThreeSum.LightThreeSumColor

end


theorem solution : ∀ {lim : Light.Limits} {μ : Nat → Int} {src n params row free k d : Nat}
  (color :
    ThreeSum.Coloring.Parameter
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.Scales.inputBits n)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (x : Fin n → Int) (hn : ThreeSum.ThreeSumWantedHostConditions.Ready k n)
  (hsrc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src n) free)
  (hparams :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) params
        (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19))))
      free)
  (hrow :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) row
        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
      free)
  (hok :
    (ThreeSum.ThreeSumFastResourcesColor.need n
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) n k)).Ok
      lim free d)
  (hread : Light.Seg μ src (@List.ofFn.{0} Int n x))
  (hx :
    ∀ (i : Fin n),
      @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (x i))
        (@Nat.cast.{0} Int instNatCastInt
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) n k)))
  (hparameters : Light.Seg μ params (ThreeSum.LightParameterInit.values n))
  (hcolor :
    Light.Seg μ row
      (@ThreeSum.ColorParameters.fields
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.Scales.inputBits n)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        color)),
  Light.Meets lim ThreeSum.LightThreeSumColor.program (@OfNat.ofNat.{0} Nat (nat_lit 509) (instOfNatNat (nat_lit 509)))
    d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt params)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt row)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt free) (@List.nil.{0} Int))))))
    μ (ThreeSum.SharedTraversalCosts.colorBudget k n) fun (r : Int) (ξ : Nat → Int) =>
    And
      (Or (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      (And
        (Iff (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@ThreeSum.ColorClassLists.witness n
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.Scales.inputBits n)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            color x))
        (Light.Kept μ ξ free)) := by
  exact @ThreeSum.LightThreeSumColor.program_meets_sourceProof

#print axioms solution
