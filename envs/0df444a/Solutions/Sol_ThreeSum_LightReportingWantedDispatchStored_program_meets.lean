-- Prove2me | solution 1 for ThreeSum.LightReportingWantedDispatchStored.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T18:44:08.052852+00:00
-- url     : https://prove2.me/submissions/0f78d12f-2221-4353-a22e-9a6b13038d87

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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_BandCandidateRows_fromOwner_sound
import Theorems.Thm_ThreeSum_BandCandidateRows_mem_records_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_row
import Theorems.Thm_ThreeSum_EncodedColorPipelineData_Stored_of_kept
import Theorems.Thm_ThreeSum_EncodedColorWantedConsumerData_incidence_length_le_magnitude
import Theorems.Thm_ThreeSum_EncodedColorWantedConsumerData_persistent_ends
import Theorems.Thm_ThreeSum_LightReportingWantedDecodeAccess_program_meets_fits
import Theorems.Thm_ThreeSum_LightReportingWantedDispatch_program_meets
import Theorems.Thm_ThreeSum_LightReportingWantedLayout_program_meets_relative
import Theorems.Thm_ThreeSum_LightReportingWantedRecordNeed_program_meets
import Theorems.Thm_ThreeSum_ReportingHostWantedRecordData_cover_scalars
import Theorems.Thm_ThreeSum_SharedReportingBankHeader_Stored_of_kept
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_WantedSourceEnds_values
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_components
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_output_count_le_magnitude
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_query_word_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_source_span_le_magnitude
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_buffers
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_decoder_word_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_depth_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_numeric_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_scratch_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_selected_ends
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_terminal_word_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_work_le


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
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
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.EncodedColorWantedConsumerData
end ThreeSum.EncodedColorWantedConsumerData
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
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
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostSourceSelection
end ThreeSum.ReportingHostSourceSelection
namespace ThreeSum.ReportingHostSourceSelectionStored
end ThreeSum.ReportingHostSourceSelectionStored
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
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
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


/-! # List and memory interfaces for the exact candidate record array -/

namespace ThreeSum.BandCandidateRows

open Light BandEnumeration

set_option maxHeartbeats 1300000















theorem records_sound {A B C : Family} {r : Record}
    (hr : r ∈ records A B C) (hf : r.flag=1) :
    r.a < A.size ∧ r.b < B.size ∧ r.c < C.size ∧
      Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (r.a,r.b,r.c) := by
  obtain ⟨o,rfl⟩ := mem_records_owner hr
  exact fromOwner_sound A B C o hf






theorem getD_sound {A B C : Family} {s : ℕ} (hs : s < (records A B C).length)
    (hf : ((records A B C).getD s default).flag=1) :
    let r := (records A B C).getD s default
    r.a < A.size ∧ r.b < B.size ∧ r.c < C.size ∧
      Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (r.a,r.b,r.c) := by
  apply records_sound _ hf
  rw [List.getD_eq_getElem _ _ hs]
  exact List.getElem_mem hs














































end ThreeSum.BandCandidateRows

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

theorem position_lt {n g i : ℕ} {rs : List Record} {l : Label}
    (hl : l ∈ firstRows n g rs i) : l.position < n := by
  have hh := (mem_row.mp (mem_firstRows.mp hl).2).2.2.2
  exact hh.trans_le (stop_le n g _)











































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


/-! # Retained local-cover tables survive reuse of the returned free region -/

namespace ThreeSum.LightLocalCoverRetention

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMetadata

set_option maxHeartbeats 1000000

theorem base_le_nextFree (base h : ℕ) : base ≤ nextFree base h := by
  unfold nextFree scheduleMaps work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr
    LightCoverGreedy.total
  omega

theorem table_ends_le (base h : ℕ) :
    maps base h+rows h*(2*(512*h)) ≤ nextFree base h ∧
    hist0 base h+rows h*localPrime h ≤ nextFree base h ∧
    hist1 base h+rows h*localPrime h ≤ nextFree base h ∧
    matrixPtr base h+rows h*cols h ≤ nextFree base h ∧
    candidates base h+scheduleSize h ≤ nextFree base h := by
  unfold nextFree scheduleMaps candidates work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr
    LightCoverGreedy.total LightCoverGreedy.out
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


/-! # Occurrence-only source-bank indices, with first block most significant -/

namespace ThreeSum.OutputDecodeOccurrenceCode

open OutputDecodeOrder OutputDecodeRecords GlobalEncoding

set_option maxHeartbeats 1500000





theorem last_lt {T M : ℕ} (hT : 0 < T) (hM : 0 < M) (k : ℕ) :
    (k%(T*M))/M < T :=
  (Nat.div_lt_iff_lt_mul hM).mpr (Nat.mod_lt _ (Nat.mul_pos hT hM))

theorem code_lt {T M : ℕ} (hT : 0 < T) (hM : 0 < M) (J k : ℕ) : code T M J k < T^J := by
  induction J generalizing k with
  | zero => simp [code]
  | succ J ih =>
    have hm := Nat.mul_le_mul_left T (show code T M J (k/(T*M))+1 ≤ T^J by exact ih _)
    have hd := last_lt hT hM k
    simp only [Nat.mul_add,Nat.mul_one] at hm
    rw [code,pow_succ']
    omega




























theorem source_code_lt (h J k : ℕ) :
    code (scheduleSize h) (layerCount h) J k < scheduleSize h^J :=
  code_lt (schedule_pos h) (layerCount_pos h) J k











end ThreeSum.OutputDecodeOccurrenceCode

end

section


/-! # Concrete source inputs from the retained normalization and wanted outputs -/

namespace ThreeSum.SourceFiniteInputs

open Light GlobalEncoding LocalCoverBounds LightLocalCoverLayout LightLocalCoverSchedule






















theorem prepared_read {μ : ℕ → ℤ} {values endpoints g : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (H : LightBandPreprocessing.Represents μ values endpoints g hg original L hs) :
    ∀ j < L.length, μ (values+j)=L.getD j 0 := fun j hj => H.1.getD hj 0







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


/-! # Finite scale bounds for every shared-bank resource component -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales Light SubsetAddress SharedReportingBankLayout SharedReportingBankHeader

set_option maxHeartbeats 3000000
set_option maxRecDepth 14000








































theorem linear_le_magnitude (n : ℕ) : 2048*(inputBits n+1) ≤ magnitude n := by
  have hh : inputBits n+1 ≤ 2^(inputBits n) := Nat.lt_two_pow_self
  calc
    _ ≤ 2048*2^(inputBits n) := Nat.mul_le_mul_left _ hh
    _ = 2^(inputBits n+11) := by rw [pow_add]; norm_num; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)










































































































































































































































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






























end ThreeSum.ThreeSumReportingSetupData

end

section


/-! # Typed contents of the executed wanted access and scratch records -/

namespace ThreeSum.ReportingHostWantedControls

open Light GlobalEncoding LocalCoverBounds LightBlockQuery ReportingHostWantedLayout







































theorem ofAccess_record (f : ℕ→ℤ) (n g : ℕ) (rs : List BandCandidateRows.Record)
    (idx pair bank cover NB NC h J cut occ code srcB srcC report : ℕ) :
    record (ofAccess f n g rs idx pair bank cover NB NC h J cut occ code srcB srcC report)=
      LightReportingWantedAccess.record f n g rs idx pair bank cover NB NC h J cut occ code srcB srcC report := rfl























end ThreeSum.ReportingHostWantedControls

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

theorem raw_stored (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    BandRawA.Stored μ (config free n A B C hsA hsB hsC).vals
      (config free n A B C hsA hsB hsC).owners (positions free n A B C hsA hsB hsC)
      (fun j => A.getD j 0) (BandRawA.items A.length (bandSize n) (records n A B C hsA hsB hsC)) :=
  H.normalized.2.2.2.2.2.2

theorem records_stored (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    Seg μ (config free n A B C hsA hsB hsC).records (BandCandidateRows.cells (records n A B C hsA hsB hsC)) :=
  H.normalized.2.2.2.2.2.1

theorem normalized_read (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    (∀ j<A.length, μ (EncodedColorLayout.av free n+j)=A.getD j 0) ∧
      (∀ j<(config free n A B C hsA hsB hsC).NB,
        μ ((config free n A B C hsA hsB hsC).srcB+j)=B.getD j 0) ∧
      (∀ j<(config free n A B C hsA hsB hsC).NC,
        μ ((config free n A B C hsA hsB hsC).srcC+j)=C.getD j 0) :=
  ⟨SourceFiniteInputs.prepared_read H.normalized.2.1,
    SourceFiniteInputs.prepared_read H.normalized.2.2.1,
    SourceFiniteInputs.prepared_read H.normalized.2.2.2.1⟩

theorem normalized_bound {U : ℕ}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hx : ∀ i, |x i|≤(U : ℤ)) :
    (∀ j<A.length, |A.getD j 0|≤(U : ℤ)) ∧
      (∀ j<(config free n A B C hsA hsB hsC).NB, |B.getD j 0|≤(U : ℤ)) ∧
      (∀ j<(config free n A B C hsA hsB hsC).NC, |C.getD j 0|≤(U : ℤ)) :=
  ThreeSumColorBudgets.normalized_values H hx

theorem incidence_length_eq (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    (config free n A B C hsA hsB hsC).N=
      (BandRawA.items A.length (bandSize n) (records n A B C hsA hsB hsC)).length :=
  BandRawA.values_length ..








































theorem incidence_value_bound {U i : ℕ}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hx : ∀ j, |x j|≤(U : ℤ)) (hi : i<(config free n A B C hsA hsB hsC).N) :
    |A.getD (BandRawA.labelAt A.length (bandSize n) (records n A B C hsA hsB hsC) i).position 0|≤(U : ℤ) := by
  rw [incidence_length_eq] at hi
  exact (normalized_bound H hx).1 _ (BandRawA.position_lt (BandRawA.at_mem hi))

theorem owner_bands {i : ℕ} (hi : i<(config free n A B C hsA hsB hsC).N) :
    (BandRawA.ownerRecord A.length (bandSize n) (records n A B C hsA hsB hsC) i).a<
      BandPartition.size A.length (bandSize n) ∧
    (BandRawA.ownerRecord A.length (bandSize n) (records n A B C hsA hsB hsC) i).b<
      BandPartition.size (config free n A B C hsA hsB hsC).NB (bandSize n) ∧
    (BandRawA.ownerRecord A.length (bandSize n) (records n A B C hsA hsB hsC) i).c<
      BandPartition.size (config free n A B C hsA hsB hsC).NC (bandSize n) := by
  rw [incidence_length_eq] at hi
  have hb := BandRawA.at_bounds hi
  have hs := BandCandidateRows.getD_sound hb.1 hb.2.1
  exact ⟨hs.1,hs.2.1,hs.2.2.1⟩

end ThreeSum.EncodedColorWantedConsumerData

end

section


/-!
# All persistent wanted-consumer inputs precede the mutable counter

The bounds use the actual packed source and wanted extents. In particular,
the pair-array endpoint is the source-control base, and the occurrence rows
end exactly at the shared source-bank header.
-/

namespace ThreeSum.EncodedColorWantedConsumerData

open Light Scales BandScales EncodedColorNormalizedData ThreeSumWantedHostData

set_option maxHeartbeats 2200000
set_option maxRecDepth 16000



















variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}


























































































theorem masks_read (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    ∀ j<(config free n A B C hsA hsB hsC).layerCount,
      μ ((config free n A B C hsA hsB hsC).masks+j)=
        (LocalMaskGraph.maskAt (512*(config free n A B C hsA hsB hsC).h)
          (2*(config free n A B C hsA hsB hsC).h) j : ℤ) := H.cover.masks

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










theorem retained_of_kept
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (HQ : ThreeSumReportingSetupData.Catalog μ free n A B C hsA hsB hsC)
    (K : Kept μ ν (config free n A B C hsA hsB hsC).counter) :
    EncodedColorPipelineData.Stored ν free n color x A B C hsA hsB hsC ∧
      ThreeSumReportingSetupData.Catalog ν free n A B C hsA hsB hsC := by
  have hbefore := ThreeSumReportingSetupData.report_le_counter free n A B C hsA hsB hsC
  have hsource : EncodedColorPipelineData.finish free n A B C hsA hsB hsC+8≤
      (config free n A B C hsA hsB hsC).counter := by
    change ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC≤
      ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC
    omega
  exact ⟨H.of_kept K hsource,SharedReportingBankHeader.Stored.of_kept HQ K le_rfl⟩


































end ThreeSum.EncodedColorWantedConsumerData

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









theorem wanted_decode_v_eq (n : ℕ) : wantedDecodeV n=(magnitude n)^4 := by
  unfold wantedDecodeV magnitude
  rw [← pow_mul]
  congr 1
  omega




































theorem wanted_left_index_le {n N i : ℕ}
    (hN : N ≤ 3*(magnitude n)^3) (hi : i<3*N) : i≤wantedDecodeV n := by
  have h9 : 9≤magnitude n := by have hh := linear_le_magnitude n; omega
  have hh : 9*(magnitude n)^3 ≤ (magnitude n)^4 := by
    calc
      _ ≤ magnitude n*(magnitude n)^3 := Nat.mul_le_mul_right _ h9
      _ = _ := by ring
  rw [wanted_decode_v_eq]
  omega

theorem wanted_right_index_le {n j : ℕ}
    (hj : j<localCount (half n)^(blocks n)) : j≤wantedDecodeV n := by
  rw [wanted_decode_v_eq]
  exact hj.le.trans ((output_count_le_magnitude n).trans
    (Nat.pow_le_pow_right (components n).positive (by decide)))



































end ThreeSum.SharedReportingBankResourceBounds

end

section


/-!
# Relative resources for the complete guarded wanted reporter

All buffer extents are relative to the caller's arbitrary free address.
Retained pointers are bounded individually by that address; they are never
summed into a purported size-only bound. Reserving frontier capacity does
not change the separately verified running time.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostWantedLayout ReportingHostFrontierLayout

set_option maxHeartbeats 2600000
set_option maxRecDepth 14000
set_option linter.unusedSectionVars false




















theorem wanted_work_eq (dst h J K N NB NC : ℕ) :
    (LightReportingWantedLayout.layout dst h J K N NB NC).work=
      dst+wantedWork h J K N NB NC := by
  unfold wantedWork LightReportingWantedLayout.layout make slot
    ReportingHostWantedLayout.root packed access decoded
  ring

theorem wanted_work_formula (h J K N NB NC : ℕ) :
    wantedWork h J K N NB NC=44+3*J+
      (K+1)*(4+2*capacityBound N NB NC (representationCap h J) (groupSize h))+
      5*groupSize h+12*2^(LightBlockQuery.width h J)+5*LightBlockQuery.width h J := by
  unfold wantedWork LightReportingWantedLayout.layout make slot
    ReportingHostWantedLayout.root packed access decoded
  ring


































































section Raw

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]







































end Raw
end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # Polynomial relative resources for every physical wanted slot -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Scales StageBounds GlobalEncoding LocalCoverBounds
open SharedReportingBankLayout ReportingHostWantedLayout

set_option maxHeartbeats 3200000
set_option maxRecDepth 16000




























































































theorem wanted_cells_le {n K N NB NC : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    wantedCells (half n) (blocks n) K N NB NC (wantedDecodeV n)≤wantedEnvelope n := by
  have hw := wanted_work_le hK hN hB hC
  have hn := wanted_numeric_le hK hN hB hC
  have hs := wanted_scratch_le n
  have h9 : (magnitude n+1)^9≤(magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h7 : (magnitude n+1)^7≤(magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h2 : (magnitude n+1)^2≤(magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  unfold wantedCells wantedEnvelope
  omega


















theorem wanted_words_le {n N : ℕ} (hN : N≤3*(magnitude n)^3) :
    LightReportingTerminal.word (half n) (blocks n)≤wantedEnvelope n ∧
    LightWantedDecode.word (wantedDecodeV n) N (half n) (blocks n)≤wantedEnvelope n ∧
    queryWord (half n) (blocks n) (BandScales.bandSize n)≤wantedEnvelope n := by
  have ht := wanted_terminal_word_le n
  have hd := wanted_decoder_word_le hN
  have hq := query_word_le n
  have h2 : (magnitude n+1)^2≤(magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h4 : (magnitude n+1)^4≤(magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h6 : (magnitude n+1)^6≤(magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  unfold wantedEnvelope queryEnvelope at *
  omega










theorem wanted_envelope_positive (n : ℕ) : 2≤wantedEnvelope n := by
  have h1 : 1≤(magnitude n+1)^10 := Nat.one_le_pow _ _ (by omega)
  unfold wantedEnvelope
  omega

noncomputable section













theorem wanted_buffers_of_ok {lim : Limits} {dst n U K N NB NC d : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hok : (wantedNeed n U).Ok lim dst d) :
    WantedBuffers lim dst (half n) (blocks n) K N NB NC (wantedDecodeV n) :=
  wanted_buffers ((Nat.add_le_add_left (wanted_cells_le hK hN hB hC) dst).trans hok.cells)

theorem wanted_envelope_word_of_ok {lim : Limits} {dst n U d : ℕ}
    (hok : (wantedNeed n U).Ok lim dst d) : (wantedEnvelope n : ℤ)≤lim.word :=
  (Int.ofNat_le.mpr (Nat.le_mul_of_pos_right _ (by omega : 0<U+1))).trans hok.word

theorem wanted_values_word_of_ok {lim : Limits} {dst n U d : ℕ}
    (hok : (wantedNeed n U).Ok lim dst d) : ((2*U : ℕ) : ℤ)≤lim.word := by
  have he := wanted_envelope_positive n
  have hb : 2*U≤wantedEnvelope n*(U+1) :=
    (Nat.mul_le_mul_left 2 (Nat.le_succ _)).trans (Nat.mul_le_mul_right _ he)
  exact (Int.ofNat_le.mpr hb).trans hok.word

theorem wanted_relative_space_of_ok {lim : Limits} {dst cover counter n U K N NB NC d : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hcover : cover+4≤dst) (hcounter : counter+3≤dst)
    (hok : (wantedNeed n U).Ok lim dst d) :
    LightReportingWantedLayout.relativeSpace dst cover counter (half n) (blocks n) K N NB NC≤lim.space := by
  have H := wanted_buffers_of_ok hK hN hB hC hok
  have hw := H.numeric
  have he := wanted_work_eq dst (half n) (blocks n) K N NB NC
  unfold wantedNumeric LightReportingWantedLayout.relativeSpace LightReportingWantedLayout.numericExtra at *
  omega

end
end ThreeSum.SharedReportingBankResourceBounds

end

section


/-!
# Concrete execution and query resources under the wanted reporter's Need

The actual two-procedure layout constructor runs once and stores the same
fourteen pointers. Every subsequent shared-catalog query uses those pointers
without constructing another catalog or clearing its reserved buffers.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light GlobalEncoding LocalCoverBounds ReportingHostWantedLayout

set_option maxHeartbeats 2200000
set_option maxRecDepth 13000

theorem wanted_words_of_ok {lim : Limits} {dst n U N d : ℕ}
    (hN : N≤3*(magnitude n)^3) (hok : (wantedNeed n U).Ok lim dst d) :
    (LightReportingTerminal.word (half n) (blocks n) : ℤ)≤lim.word ∧
    (LightWantedDecode.word (wantedDecodeV n) N (half n) (blocks n) : ℤ)≤lim.word ∧
    (queryWord (half n) (blocks n) (BandScales.bandSize n) : ℤ)≤lim.word := by
  obtain ⟨ht,hd,hq⟩ := wanted_words_le hN
  have hw := wanted_envelope_word_of_ok hok
  exact ⟨(Int.ofNat_le.mpr ht).trans hw,(Int.ofNat_le.mpr hd).trans hw,(Int.ofNat_le.mpr hq).trans hw⟩


















theorem wanted_integer_word_of_ok {lim : Limits} {dst n U d : ℕ} {z : ℤ}
    (hz : |z|≤(U : ℤ)) (hok : (wantedNeed n U).Ok lim dst d) : |z|≤lim.word := by
  have hh := wanted_values_word_of_ok hok
  have hu : (0 : ℤ)≤(U : ℤ) := Int.natCast_nonneg _
  push_cast at hh
  omega









theorem wanted_depth_of_ok {lim : Limits} {dst n U K N NB NC d : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hok : (wantedNeed n U).Ok lim dst d) :
    d+wantedDepth (half n) (blocks n) K N NB NC≤lim.depth :=
  (Nat.add_le_add_left (wanted_depth_le hK hN hB hC) d).trans hok.depth






















theorem wanted_layout_meets {lim : Limits} {μ : ℕ→ℤ} {dst cover counter n U K N NB NC d : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hcover : cover+4≤dst) (hcounter : counter+3≤dst)
    (hgroup : μ (cover+3)=(groupSize (half n) : ℤ))
    (hcap : μ (counter+2)=(representationCap (half n) (blocks n) : ℤ))
    (hok : (wantedNeed n U).Ok lim dst d) :
    Meets lim LightReportingWantedLayout.program 1 d
      [blocks n,half n,K,cover,counter,N,NB,NC,dst] μ
      (LightReportingWantedLayout.time (half n) (blocks n))
      (fun result ν =>
        result=((LightReportingWantedLayout.layout dst (half n) (blocks n) K N NB NC).work : ℤ) ∧
        SegN ν dst (values (LightReportingWantedLayout.layout dst (half n) (blocks n) K N NB NC)) ∧
        SameOutside μ ν dst 14) := by
  have hd := hok.depth
  have he := wanted_envelope_positive n
  change d+wantedEnvelope n≤lim.depth at hd
  exact LightReportingWantedLayout.program_meets_relative hgroup hcap hok.space (by omega)
    (wanted_relative_space_of_ok hK hN hB hC hcover hcounter hok)

end ThreeSum.SharedReportingBankResourceBounds

end

section


/-!
# Every selected persistent row remains before the counter

The bounds keep the selected B and C bands independent. Each incidence and
occurrence is selected by its retained physical label, and every translated
pointer is bounded individually by the already occupied prefix.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light GlobalEncoding LocalCoverBounds BlockSourceEncoding
open ReportingHostSourceSelection ReportingHostSourceSelectionStored

set_option maxHeartbeats 2800000
set_option maxRecDepth 15000














theorem wanted_cover_ends (cover h J : ℕ) :
    cover+20≤LightCoverKeyData.keyEnd cover h J ∧
    LightLocalCoverLayout.scheduleMaps (LightLocalCoverInit.base cover) h+2*(512*h)*scheduleSize h≤
      LightCoverKeyData.keyEnd cover h J ∧
    LightLocalCoverLayout.candidates (LightLocalCoverInit.base cover) h+scheduleSize h≤
      LightCoverKeyData.keyEnd cover h J ∧
    LightLocalCoverLayout.hist0 (LightLocalCoverInit.base cover) h+LightLocalCoverSchedule.rows h*localPrime h≤
      LightCoverKeyData.keyEnd cover h J ∧
    LightLocalCoverLayout.hist1 (LightLocalCoverInit.base cover) h+LightLocalCoverSchedule.rows h*localPrime h≤
      LightCoverKeyData.keyEnd cover h J := by
  have hb := LightLocalCoverRetention.base_le_nextFree (LightLocalCoverInit.base cover) h
  have ht := LightLocalCoverRetention.table_ends_le (LightLocalCoverInit.base cover) h
  have he := LightCoverKeyData.afterCover_le_keyEnd cover h J
  change LightLocalCoverMetadata.nextFree (LightLocalCoverInit.base cover) h≤_ at he
  refine ⟨hb.trans he,?_,ht.2.2.2.2.trans he,ht.2.1.trans he,ht.2.2.1.trans he⟩
  simpa only [LightLocalCoverMetadata.nextFree,Nat.mul_comm] using he



















































































































end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # Individual selector bounds from the proved wanted Need -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light GlobalEncoding LocalCoverBounds ReportingHostWantedLayout
open ReportingHostSourceSelection ReportingHostSourceSelectionStored

set_option maxHeartbeats 2300000
set_option maxRecDepth 14000

theorem WantedSourceEnds.fits {X : Pointers}
    {pair bank cover srcB srcC i j code h J cut stop out limit : ℕ}
    (H : WantedSourceEnds X pair bank cover srcB srcC i j code h J cut stop)
    (hs : stop≤limit) (hout : out+15≤limit) (hscalar : J+X.bankSpan+20≤limit) :
    ReportingHostSourceSelection.Fits X pair bank cover srcB srcC i j code J out limit := by
  refine ⟨H.pairHeader.trans hs,H.bankHeader.trans hs,H.coverHeader.trans hs,hout,
    H.leftHead.trans hs,H.rightHead.trans hs,H.leftCell.trans hs,H.rightCell.trans hs,
    ?_,hscalar,fun v hv => (H.values v hv).trans hs⟩
  exact (Nat.le_add_right _ _).trans (H.occurrence.trans hs)

theorem wanted_selector_scalars_le (n : ℕ) :
    blocks n+SourceBandBankLayout.span (half n) (blocks n) (LightBlockQuery.sourceCut (half n) (blocks n))+20≤
      wantedEnvelope n := by
  have hs := source_span_le_magnitude n
  have hj := (components n).blocksBound
  have hm : magnitude n≤(magnitude n+1)^10 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  have h3 : (magnitude n+1)^3≤(magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h1 : 1≤(magnitude n+1)^10 := Nat.one_le_pow _ _ (by omega)
  unfold wantedEnvelope LightBlockQuery.sourceCut
  omega


















theorem wanted_access_output_le {lim : Limits} {dst n U K N NB NC d : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hok : (wantedNeed n U).Ok lim dst d) :
    ReportingHostWantedLayout.access dst (blocks n)+20≤lim.space := by
  have H := wanted_buffers_of_ok hK hN hB hC hok
  have hw := H.numeric
  have he := wanted_work_eq dst (half n) (blocks n) K N NB NC
  have hf := wanted_work_formula (half n) (blocks n) K N NB NC
  unfold ReportingHostWantedLayout.access decoded
  omega

theorem wanted_source_fits_of_ok {lim : Limits}
    {pair bank cover srcB srcC NB NC n U occ i j code stop dst out d : ℕ}
    (H : WantedSourceEnds
      (retained pair bank cover NB NC (BandScales.bandSize n) (half n) (blocks n)
        (LightBlockQuery.sourceCut (half n) (blocks n)) occ i j code)
      pair bank cover srcB srcC i j code (half n) (blocks n)
        (LightBlockQuery.sourceCut (half n) (blocks n)) stop)
    (hstop : stop≤dst) (hout : out+15≤lim.space)
    (hok : (wantedNeed n U).Ok lim dst d) :
    ReportingHostSourceSelection.Fits
      (retained pair bank cover NB NC (BandScales.bandSize n) (half n) (blocks n)
        (LightBlockQuery.sourceCut (half n) (blocks n)) occ i j code)
      pair bank cover srcB srcC i j code (blocks n) out lim.space := by
  have he := hok.cells
  have hs : wantedEnvelope n≤lim.space := by change dst+wantedEnvelope n≤lim.space at he; omega
  exact H.fits (by omega) hout ((wanted_selector_scalars_le n).trans hs)

theorem wanted_access_fits_of_ok {lim : Limits}
    {pair bank cover srcB srcC NB NC n U K N occ i j code stop dst d : ℕ}
    (H : WantedSourceEnds
      (retained pair bank cover NB NC (BandScales.bandSize n) (half n) (blocks n)
        (LightBlockQuery.sourceCut (half n) (blocks n)) occ i j code)
      pair bank cover srcB srcC i j code (half n) (blocks n)
        (LightBlockQuery.sourceCut (half n) (blocks n)) stop)
    (hstop : stop≤dst) (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hok : (wantedNeed n U).Ok lim dst d) :
    ReportingHostSourceSelection.Fits
      (retained pair bank cover NB NC (BandScales.bandSize n) (half n) (blocks n)
        (LightBlockQuery.sourceCut (half n) (blocks n)) occ i j code)
      pair bank cover srcB srcC i j code (blocks n)
      (ReportingHostWantedLayout.access dst (blocks n)+5) lim.space :=
  wanted_source_fits_of_ok H hstop (by have hh := wanted_access_output_le hK hN hB hC hok; omega) hok

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

theorem cut_eq_mu (n : ℕ) : LightBlockQuery.sourceCut (half n) (blocks n)=mu n := by
  unfold LightBlockQuery.sourceCut half blocks mu totalSize microSize microHalf
  ring

theorem depth_le_blocks (n : ℕ) : LightSwitchDepth.depth (blocks n)≤blocks n := by
  unfold LightSwitchDepth.depth
  omega













































variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}


























































end ThreeSum.ReportingHostWantedConsumerData

end

section


/-!
# Run an actual physical wanted slot from the retained encoded color

The slot's original label and two physical integer indices are supplied by
the emitted array. Every source, catalog, mask, allocation and selected
value used by the fixed152 executable is derived from the retained payload.
-/

namespace ThreeSum.LightReportingWantedDispatchStored

open Light Scales BandScales BandRawA RawReporting RawIncidences GlobalEncoding
open EncodedColorNormalizedData EncodedColorWantedConsumerData ThreeSumWantedHostData
open ReportingHostWantedOriginal ReportingHostWantedPhysical ReportingHostWantedLayout
open ReportingHostWantedConsumerData SharedReportingBankResourceBounds

set_option maxHeartbeats 3800000
set_option maxRecDepth 24000
set_option linter.unusedSectionVars false

theorem program_meets_sourceProof {lim : Limits} {μ : ℕ→ℤ} {free n U d s raw output old threshold : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (HQ : ThreeSumReportingSetupData.Catalog μ free n A B C hsA hsB hsC)
    (hx : ∀ i, |x i|≤(U : ℤ))
    (w : Label n A B C hsA hsB hsC)
    (hs : s<count n A B C hsA hsB hsC)
    (hraw : raw<3*(config free n A B C hsA hsB hsC).N)
    (hout : output<OutputDecodeRecords.localCount (half n)^blocks n)
    (hpos : w.1.val=raw%(config free n A B C hsA hsB hsC).N)
    (he : w.2.2=LightOutputDecodeOriginal.output (half n) (blocks n) output)
    (hleft : μ ((config free n A B C hsA hsB hsC).pairs+2*s)=(raw : ℤ))
    (hright : μ ((config free n A B C hsA hsB hsC).pairs+2*s+1)=(output : ℤ))
    (hp : 0<EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (hguard : 4*(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)≤globalModulus (half n) (blocks n))
    (hkey : globalModulus (half n) (blocks n) ∣
      valueAt A.length (bandSize n) (records n A B C hsA hsB hsC) (fun j => A.getD j 0) w.1.val %
        (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)+
      lift w.2.1*(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)+
      ThreeSumReportingSetupData.shift n A B C hsA hsB hsC-globalKey w.2.2)
    (hcounter : μ (config free n A B C hsA hsB hsC).counter=(old : ℤ))
    (hthreshold : μ ((config free n A B C hsA hsB hsC).counter+1)=(threshold : ℤ))
    (hcap : μ ((config free n A B C hsA hsB hsC).counter+2)=(representationCap (half n) (blocks n) : ℤ))
    (hold : old≤3*(magnitude n)^7)
    (hmass : labelMass n A B C hsA hsB hsC w≤3*(magnitude n)^7)
    (hthresholdBound : threshold≤9*(magnitude n)^8)
    (hok : (wantedNeed n U).Ok lim (config free n A B C hsA hsB hsC).layoutHeader (d+1)) :
    Meets lim LightReportingWantedDispatch.program 151 d
      (LightReportingWantedDispatch.arguments (config free n A B C hsA hsB hsC) s) μ
      (LightReportingWantedDispatch.time (config free n A B C hsA hsB hsC) (wantedDecodeV n)
        (recordTime free n A B C hsA hsB hsC w output old threshold))
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ threshold<old+labelMass n A B C hsA hsB hsC w ∨ labelHit n A B C hsA hsB hsC w) ∧
        ν (config free n A B C hsA hsB hsC).counter=((old+labelMass n A B C hsA hsB hsC w : ℕ) : ℤ) ∧
        KeptBut μ ν (config free n A B C hsA hsB hsC).layoutHeader
          (config free n A B C hsA hsB hsC).counter 1) := by
  let cfg := config free n A B C hsA hsB hsC
  let rs := records n A B C hsA hsB hsC
  let L := LightReportingWantedLayout.layout cfg.layoutHeader cfg.h cfg.J cfg.K cfg.N cfg.NB cfg.NC
  let occ := occurrence free n A B C hsA hsB hsC
  let code := OutputDecodeOccurrenceCode.code cfg.scheduleSize cfg.layerCount cfg.J output
  let S := ReportingHostWantedRecordData.selected (fun j => A.getD j 0) A.length B.length C.length
    (bandSize n) cfg.pair cfg.bank cfg.cover cfg.h cfg.J occ cfg.srcB cfg.srcC cfg.report rs w output
  let Q := fun (r : ℤ) ν => (r=0 ∨ r=1) ∧
    (r=1 ↔ threshold<old+labelMass n A B C hsA hsB hsC w ∨ labelHit n A B C hsA hsB hsC w) ∧
    ν cfg.counter=((old+labelMass n A B C hsA hsB hsC w : ℕ) : ℤ) ∧
    KeptBut μ ν cfg.layoutHeader cfg.counter 1
  have hNI : cfg.N=(items A.length (bandSize n) rs).length := incidence_length_eq ..
  have hNI0 := incidence_length_eq free n A B C hsA hsB hsC
  have hL : L=LightReportingWantedLayout.layout cfg.layoutHeader (half n) (blocks n)
      (LightSwitchDepth.depth (blocks n)) (items A.length (bandSize n) rs).length B.length C.length := by
    dsimp only [L]
    rw [hNI]
    rfl
  have hSL : S.NL=leftCount rs B.length w := rfl
  have hSR : S.NR=rightCount rs C.length w := rfl
  have hpos' : w.1.val=raw%(items A.length (bandSize n) rs).length := hpos.trans (congrArg (raw%·) hNI)
  have hpos0 : w.1.val=raw%(items A.length (bandSize n) (records n A B C hsA hsB hsC)).length := hpos'
  have hi : w.1.val<cfg.N := by rw [hNI]; exact w.1.isLt
  obtain ⟨_,hiB,hiC⟩ := owner_bands hi
  have hB := (ThreeSumColorBudgets.normalized_lengths H).2.1
  have hC := (ThreeSumColorBudgets.normalized_lengths H).2.2
  have hN : cfg.N≤3*(magnitude n)^3 := incidence_length_le_magnitude H
  have hN' : (items A.length (bandSize n) rs).length≤3*(magnitude n)^3 := by rw [← hNI]; exact hN
  have hK : cfg.K≤blocks n := depth_le_blocks n
  have hends : PersistentEnds cfg (positions free n A B C hsA hsB hsC) occ (bandSize n) (mu n)
      rs.length (count n A B C hsA hsB hsC) := persistent_ends H
  have hbank : SourceBandBankData.finish cfg.bank B.length C.length (bandSize n) (half n) (blocks n)
      (LightBlockQuery.sourceCut (half n) (blocks n))≤cfg.report := by
    rw [cut_eq_mu]
    exact hends.bank
  have hreport : SharedReportingBankHeader.finish cfg.report cfg.h cfg.J cfg.NB cfg.NC (bandSize n)≤cfg.counter := hends.report
  have hbefore : cfg.counter+4=cfg.layoutHeader := rfl
  have hc : cfg.counter≤cfg.layoutHeader := by dsimp only [cfg,rs] at *; omega
  have hbuf := wanted_buffers_of_ok hK hN hB hC hok
  have hdep := wanted_depth_of_ok hK hN hB hC hok
  have hd50 : d+1+50≤lim.depth :=
    (Nat.add_le_add_left (show 50≤wantedDepth (half n) (blocks n) cfg.K cfg.N B.length C.length from
      Nat.le_add_left 50 _) (d+1)).trans hdep
  have hd : d+5<lim.depth := by dsimp only [cfg,rs] at *; omega
  have haccess : access cfg.layoutHeader cfg.J+20≤lim.space := wanted_access_output_le hK hN hB hC hok
  have hspace : cfg.layoutHeader+38+2*cfg.J≤lim.space := by
    unfold access decoded at haccess
    dsimp only [cfg,rs] at *; omega
  have hg : cfg.cover+4≤cfg.layoutHeader := by
    have hh := (wanted_cover_ends cfg.cover cfg.h cfg.J).1.trans hends.cover
    dsimp only [cfg,rs] at *; omega
  have hcode : code<LightBlockSourceCatalog.count cfg.h cfg.J :=
    OutputDecodeOccurrenceCode.source_code_lt cfg.h cfg.J output
  have hselectedEnds := wanted_selected_ends (occ := occ) (cut := LightBlockQuery.sourceCut (half n) (blocks n))
    (BandScales.bandSize_pos n) hiB hiC hcode hends.srcB hends.srcC hends.pair
    (hbank.trans (by have hb := hends.reportBeforeCounter; dsimp only [cfg,rs] at *; omega)) hends.occurrence hends.cover
  have hfit := wanted_access_fits_of_ok (N := cfg.N) hselectedEnds hc hK hN hB hC hok
  have hval := incidence_value_bound H hx hi
  have hvalWord := wanted_integer_word_of_ok hval hok
  let AP := fun ν => SegN ν cfg.layoutHeader (ReportingHostWantedLayout.values L) ∧ Kept μ ν cfg.layoutHeader
  let BP := fun ν => LightWantedDecode.Stored ν (decoded cfg.layoutHeader)
      (items A.length (bandSize n) rs).length cfg.h cfg.J raw output ∧
    Seg ν (access cfg.layoutHeader cfg.J) (ReportingHostWantedControls.record S) ∧
    SegN ν cfg.layoutHeader (ReportingHostWantedLayout.values L) ∧ Kept μ ν cfg.layoutHeader
  have retained (ν : ℕ→ℤ) (hk : Kept μ ν cfg.layoutHeader) :=
    retained_of_kept H HQ (fun a ha => hk a (ha.trans_le hc))
  apply LightReportingWantedDispatch.program_meets (L := L) (A := AP) (B := BP) (Q := Q)
    hok.space (by dsimp only [cfg,rs] at *; omega) hspace
  · have hgRead := (ReportingHostWantedRecordData.cover_scalars H.cover).1
    exact (wanted_layout_meets hK hN hB hC hg (by dsimp only [cfg,rs] at *; omega) hgRead hcap hok).mono le_rfl
      (fun r ν hr => ⟨hr.1,hr.2.1,fun a ha => hr.2.2 a (Or.inl ha)⟩)
  · intro ν hν
    obtain ⟨Hν,HQν⟩ := retained ν hν.2
    have HBν : SourceBandBankData.Stored ν (fun j => B.getD j 0) (fun j => C.getD j 0)
        cfg.bank B.length C.length (bandSize n) (half n) (blocks n)
        (LightBlockQuery.sourceCut (half n) (blocks n)) occ
        (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)
        (ThreeSumReportingSetupData.shift n A B C hsA hsB hsC) := by
      rw [cut_eq_mu]
      exact Hν.sources.banks
    have hraw' : raw<3*(items A.length (bandSize n) rs).length := by rw [← hNI]; exact hraw
    have hiB' : (ownerRecord A.length (bandSize n) rs (raw%(items A.length (bandSize n) rs).length)).b<
        BandPartition.size B.length (bandSize n) := by rw [← hpos']; exact hiB
    have hiC' : (ownerRecord A.length (bandSize n) rs (raw%(items A.length (bandSize n) rs).length)).c<
        BandPartition.size C.length (bandSize n) := by rw [← hpos']; exact hiC
    have hdecode := LightReportingWantedDecodeAccess.program_meets_fits (d := d+1)
      (decoded := decoded cfg.layoutHeader) (dst := access cfg.layoutHeader cfg.J) (work := L.work)
      (n := A.length) (g := bandSize n) (rs := rs) (NB := B.length) (NC := C.length)
      (h := half n) (J := blocks n) (pair := cfg.pair) (bank := cfg.bank) (cover := cfg.cover)
      (srcB := cfg.srcB) (srcC := cfg.srcC) (report := cfg.report) (occ := occ)
      (pairs := cfg.pairs) (slot := s) (masks := cfg.masks)
      (raw_stored Hν) (records_stored Hν) hraw' hout
      (wanted_left_index_le hN hraw) (wanted_right_index_le hout)
      Hν.sources.buckets HBν Hν.cover HQν hiB' hiC' hok.space (by dsimp only [cfg,rs] at *; omega)
      (by have hh := hends.values; rw [hNI] at hh; unfold decoded; dsimp only [cfg,rs] at *; omega)
      (by have hh := hends.owners; rw [hNI] at hh; unfold decoded; dsimp only [cfg,rs] at *; omega)
      (by have hh := hends.positions; rw [hNI] at hh; unfold decoded; dsimp only [cfg,rs] at *; omega)
      (by have hh := hends.records; unfold decoded; dsimp only [cfg,rs] at *; omega)
      (hends.srcB.trans (by unfold decoded; omega))
      (hends.srcC.trans (by unfold decoded; omega))
      (hends.pair.trans (by unfold decoded; omega))
      (hbank.trans (by have hh := hends.reportBeforeCounter; unfold decoded; omega))
      hends.occurrence (hends.cover.trans (by unfold decoded; omega))
      (hends.report.trans (by unfold decoded; omega))
      (by unfold access; rfl)
      (by have hh := wanted_work_eq cfg.layoutHeader cfg.h cfg.J cfg.K cfg.N cfg.NB cfg.NC
          have hf := wanted_work_formula cfg.h cfg.J cfg.K cfg.N cfg.NB cfg.NC
          change access cfg.layoutHeader cfg.J+20≤
            (LightReportingWantedLayout.layout cfg.layoutHeader cfg.h cfg.J cfg.K cfg.N cfg.NB cfg.NC).work
          unfold access decoded
          dsimp only [cfg,rs] at *; omega)
      (by have hh := hends.pairs; unfold decoded; dsimp only [cfg,rs] at *; omega)
      (hends.masks.trans (by unfold decoded; omega))
      ((hν.2 _ (by have hh := hends.pairs; dsimp only [cfg,rs] at *; omega)).trans hleft)
      ((hν.2 _ (by have hh := hends.pairs; dsimp only [cfg,rs] at *; omega)).trans hright)
      (masks_read Hν) hbuf.decoder (by simpa only [cfg,rs,hNI0] using (wanted_words_of_ok hN hok).2.1)
      (by simpa only [code,cfg,rs,config,half,blocks,LightReportingWantedAccess.selection,← hpos0] using hfit)
      (by simpa only [cfg,rs,← hpos0] using hvalWord)
    have hdecode' := hdecode.mono (R' := fun _ ξ => BP ξ) le_rfl (fun _ ξ hr => by
      refine ⟨hr.2.1,?_,?_,?_⟩
      · simpa only [S,ReportingHostWantedRecordData.selected,ReportingHostWantedControls.ofAccess_record,
          cfg,rs,config,half,blocks,← hpos0] using hr.2.2.1
      · exact hν.1.of_kept hr.2.2.2 (by simp only [ReportingHostWantedLayout.values,List.length_map,List.length_cons,List.length_nil,decoded]; omega)
      · exact fun a ha => (hr.2.2.2 a (by unfold decoded; dsimp only [cfg,rs] at *; omega)).trans (hν.2 a ha))
    simpa only [LightReportingWantedDispatch.decodeArguments,cfg,rs,config,half,blocks,incidences,
      BandRawA.values_length,EncodedColorWantedConsumerData.records] using hdecode'
  · intro ν hν
    obtain ⟨Hν,HQν⟩ := retained ν hν.2.2.2
    have HBν : SourceBandBankData.Stored ν (fun j => B.getD j 0) (fun j => C.getD j 0)
        cfg.bank B.length C.length (bandSize n) (half n) (blocks n)
        (LightBlockQuery.sourceCut (half n) (blocks n)) occ
        (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)
        (ThreeSumReportingSetupData.shift n A B C hsA hsB hsC) := by
      rw [cut_eq_mu]
      exact Hν.sources.banks
    have hrun := LightReportingWantedRecordNeed.program_meets (d := d+1)
      (pair := cfg.pair) (bank := cfg.bank) (cover := cfg.cover) (occ := occ)
      (srcB := cfg.srcB) (srcC := cfg.srcC) (report := cfg.report) (records := cfg.records)
      (dst := cfg.layoutHeader) (counter := cfg.counter) (K := cfg.K) w
      Hν.sources.buckets HBν Hν.cover HQν hiB hiC hout he hp hguard le_rfl hK hkey
      hν.2.1 (by have hh := hν.2.2.1; rw [hL] at hh; exact hh) hν.1 (by omega)
      ((hν.2.2.2 _ (by dsimp only [cfg,rs] at *; omega)).trans hcounter)
      ((hν.2.2.2 _ (by dsimp only [cfg,rs] at *; omega)).trans hthreshold)
      hselectedEnds hends.records hends.srcB hends.srcC hbank hreport hN' hB hC
      hold hmass hthresholdBound (normalized_read Hν).2.1 (normalized_read Hν).2.2
      (normalized_bound H hx).2.1 (normalized_bound H hx).2.2 hval hok
    have hrun' := hrun.mono (R' := Q) le_rfl (fun r ξ hr => by
      refine ⟨hr.1,hr.2.1,hr.2.2.1,?_⟩
      intro a ha
      exact (hr.2.2.2 a ⟨by unfold packed access decoded; dsimp only [cfg,rs] at *; omega,ha.2⟩).trans (hν.2.2.2 a ha.1))
    dsimp only [S,cfg,rs,config,half,blocks] at hSL hSR
    simpa only [LightReportingWantedDispatch.recordArguments,recordTime,labelMass,labelHit,fiber,
      hSL,hSR,cfg,config,half,blocks,BlockSourceEncoding.modulus,Scales.radix,Scales.localRadix,
      ThreeSumReportingSetupData.shift] using hrun'

end ThreeSum.LightReportingWantedDispatchStored

end


theorem solution : ∀ {lim : Light.Limits} {μ : Nat → Int} {free n U d s raw output old threshold : Nat}
  {color :
    ThreeSum.Coloring.Parameter
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.Scales.inputBits n)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
  {x : Fin n → Int} {A B C : List.{0} Int}
  {hsA : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) A}
  {hsB : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) B}
  {hsC : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) C}
  (H : ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
  (HQ : ThreeSum.ThreeSumReportingSetupData.Catalog μ free n A B C hsA hsB hsC)
  (hx :
    ∀ (i : Fin n),
      @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (x i))
        (@Nat.cast.{0} Int instNatCastInt U))
  (w : ThreeSum.ReportingHostWantedConsumerData.Label n A B C hsA hsB hsC)
  (hs : @LT.lt.{0} Nat instLTNat s (ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC))
  (hraw :
    @LT.lt.{0} Nat instLTNat raw
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).N))
  (hout :
    @LT.lt.{0} Nat instLTNat output
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (ThreeSum.OutputDecodeRecords.localCount (ThreeSum.SharedReportingBankResourceBounds.half n))
        (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
  (hpos :
    @Eq.{1} Nat
      (@Fin.val
        (@List.length.{0} ThreeSum.BandRawA.Label
          (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n)
            (ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC)))
        (@Prod.fst.{0, 0}
          (ThreeSum.ReportingHostWantedOriginal.AType (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n)
            (ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC))
          (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
              (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
          w))
      (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) raw
        (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).N))
  (he :
    @Eq.{1}
      (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n))
      (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n))
        (@Prod.snd.{0, 0}
          (ThreeSum.ReportingHostWantedOriginal.AType (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n)
            (ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC))
          (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
              (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
          w))
      (ThreeSum.LightOutputDecodeOriginal.output (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n) output))
  (hleft :
    @Eq.{1} Int
      (μ
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).pairs
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) s)))
      (@Nat.cast.{0} Int instNatCastInt raw))
  (hright :
    @Eq.{1} Int
      (μ
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).pairs
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) s))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Nat.cast.{0} Int instNatCastInt output))
  (hp :
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC))
  (hguard :
    @LE.le.{0} Int Int.instLEInt
      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
        (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))
        (@Nat.cast.{0} Int instNatCastInt (ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)))
      (ThreeSum.GlobalEncoding.globalModulus (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
  (hkey :
    @Dvd.dvd.{0} Int Int.instDvd
      (ThreeSum.GlobalEncoding.globalModulus (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n))
      (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
            (@HMod.hMod.{0, 0, 0} Int Int Int (@instHMod.{0} Int Int.instMod)
              (ThreeSum.BandRawA.valueAt (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n)
                (ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC)
                (fun (j : Nat) => @List.getD.{0} Int A j (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
                (@Fin.val
                  (@List.length.{0} ThreeSum.BandRawA.Label
                    (ThreeSum.BandRawA.items (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n)
                      (ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC)))
                  (@Prod.fst.{0, 0}
                    (ThreeSum.ReportingHostWantedOriginal.AType (@List.length.{0} Int A)
                      (ThreeSum.BandScales.bandSize n)
                      (ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC))
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                        (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
                    w)))
              (@Nat.cast.{0} Int instNatCastInt (ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)))
            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
              (ThreeSum.RawIncidences.lift
                (@Prod.fst.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                    (ThreeSum.SharedReportingBankResourceBounds.blocks n))
                  (@Prod.snd.{0, 0}
                    (ThreeSum.ReportingHostWantedOriginal.AType (@List.length.{0} Int A)
                      (ThreeSum.BandScales.bandSize n)
                      (ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC))
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                        (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
                    w)))
              (@Nat.cast.{0} Int instNatCastInt (ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC))))
          (ThreeSum.ThreeSumReportingSetupData.shift n A B C hsA hsB hsC))
        (@ThreeSum.GlobalEncoding.globalKey (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n)
          (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
              (ThreeSum.SharedReportingBankResourceBounds.blocks n))
            (@Prod.snd.{0, 0}
              (ThreeSum.ReportingHostWantedOriginal.AType (@List.length.{0} Int A) (ThreeSum.BandScales.bandSize n)
                (ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC))
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                  (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
              w)))))
  (hcounter :
    @Eq.{1} Int (μ (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter)
      (@Nat.cast.{0} Int instNatCastInt old))
  (hthreshold :
    @Eq.{1} Int
      (μ
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Nat.cast.{0} Int instNatCastInt threshold))
  (hcap :
    @Eq.{1} Int
      (μ
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@Nat.cast.{0} Int instNatCastInt
        (ThreeSum.GlobalEncoding.representationCap (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n))))
  (hold :
    @LE.le.{0} Nat instLENat old
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (ThreeSum.SharedReportingBankResourceBounds.magnitude n)
          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
  (hmass :
    @LE.le.{0} Nat instLENat (ThreeSum.ReportingHostWantedConsumerData.labelMass n A B C hsA hsB hsC w)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (ThreeSum.SharedReportingBankResourceBounds.magnitude n)
          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
  (hthresholdBound :
    @LE.le.{0} Nat instLENat threshold
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (ThreeSum.SharedReportingBankResourceBounds.magnitude n)
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))
  (hok :
    (ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim
      (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).layoutHeader
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
  Light.Meets lim ThreeSum.LightReportingWantedDispatch.program
    (@OfNat.ofNat.{0} Nat (nat_lit 151) (instOfNatNat (nat_lit 151))) d
    (ThreeSum.LightReportingWantedDispatch.arguments (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC)
      s)
    μ
    (ThreeSum.LightReportingWantedDispatch.time (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC)
      (ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n)
      (ThreeSum.ReportingHostWantedConsumerData.recordTime free n A B C hsA hsB hsC w output old threshold))
    fun (r : Int) (ν : Nat → Int) =>
    And
      (Or (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      (And
        (Iff (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Or
            (@LT.lt.{0} Nat instLTNat threshold
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
                (ThreeSum.ReportingHostWantedConsumerData.labelMass n A B C hsA hsB hsC w)))
            (ThreeSum.ReportingHostWantedConsumerData.labelHit n A B C hsA hsB hsC w)))
        (And
          (@Eq.{1} Int (ν (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter)
            (@Nat.cast.{0} Int instNatCastInt
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
                (ThreeSum.ReportingHostWantedConsumerData.labelMass n A B C hsA hsB hsC w))))
          (Light.KeptBut μ ν (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).layoutHeader
            (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := by
  exact @ThreeSum.LightReportingWantedDispatchStored.program_meets_sourceProof

#print axioms solution
