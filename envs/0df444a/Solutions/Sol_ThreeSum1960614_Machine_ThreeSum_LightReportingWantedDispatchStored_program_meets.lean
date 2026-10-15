-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatchStored.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:05:32.607181+00:00
-- url     : https://prove2.me/submissions/3a407fae-ea80-49f2-a49e-32e1430e53be

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorPipelineData_Stored_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorWantedConsumerData_incidence_length_le_magnitude
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorWantedConsumerData_persistent_ends
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingWantedDecodeAccess_program_meets_fits
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingWantedDispatch_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingWantedLayout_program_meets_relative
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingWantedRecordNeed_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_ReportingHostWantedRecordData_cover_scalars
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankHeader_Stored_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_WantedSourceEnds_values
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_components
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_output_count_le_magnitude
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_query_word_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_source_span_le_magnitude
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_buffers
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_decoder_word_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_depth_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_numeric_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_scratch_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_selected_ends
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_terminal_word_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_work_le
import Theorems.Thm_ThreeSum_BandCandidateRows_fromOwner_sound
import Theorems.Thm_ThreeSum_BandCandidateRows_mem_records_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_row

local instance platformRadixNonzero_b9650ad5db (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Filter
end Filter
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
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.EncodedColorWantedConsumerData
end ThreeSum.EncodedColorWantedConsumerData
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightColorBands
end ThreeSum.LightColorBands
namespace ThreeSum.LightCoverKeyData
end ThreeSum.LightCoverKeyData
namespace ThreeSum.LightLocalCoverRetention
end ThreeSum.LightLocalCoverRetention
namespace ThreeSum.LightReportingWantedDispatchStored
end ThreeSum.LightReportingWantedDispatchStored
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.OutputDecodeOccurrenceCode
end ThreeSum.OutputDecodeOccurrenceCode
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostSourceSelection
end ThreeSum.ReportingHostSourceSelection
namespace ThreeSum.ReportingHostWantedConsumerData
end ThreeSum.ReportingHostWantedConsumerData
namespace ThreeSum.ReportingHostWantedControls
end ThreeSum.ReportingHostWantedControls
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum.ReportingHostWantedPhysical
end ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows
namespace ThreeSum.SourceFiniteInputs
end ThreeSum.SourceFiniteInputs
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.ThreeSumColorBudgets
end ThreeSum.ThreeSumColorBudgets
namespace ThreeSum.ThreeSumReportingSetupData
end ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BandEnumeration
end ThreeSum1960614.Machine.ThreeSum.BandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.ColorClassLists
end ThreeSum1960614.Machine.ThreeSum.ColorClassLists
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightClassFilter
end ThreeSum1960614.Machine.ThreeSum.LightClassFilter
namespace ThreeSum1960614.Machine.ThreeSum.LightColorBands
end ThreeSum1960614.Machine.ThreeSum.LightColorBands
namespace ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData
end ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatchStored
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatchStored
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows
namespace ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs
end ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets
end ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
end ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
end ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

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













/-- Reading a cell of a segment, with a default value for the list. -/
theorem Seg.getD (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) {i : ℕ} (hi : i < l.length) (d : ℤ) : μ (a + i) = l.getD i d := by
  rw [h i hi, List.getD_eq_getElem _ _ hi]











/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : _root_.ThreeSum1960614.Machine.Light.Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]









/-- A segment all of whose cells are kept. -/
theorem Seg.of_sameOn {K : ℕ → Prop} (h : _root_.ThreeSum1960614.Machine.Light.Seg μ b l) (hs : _root_.ThreeSum1960614.Machine.Light.SameOn K μ μ')
    (hK : ∀ i < l.length, K (b + i)) : _root_.ThreeSum1960614.Machine.Light.Seg μ' b l := h.congr fun i hi => hs _ (hK i hi)











































end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # List and memory interfaces for the exact candidate record array -/

namespace ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandCandidateRows


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration

set_option maxHeartbeats 1300000



theorem records_sound {A B C : _root_.ThreeSum.BandEnumeration.Family} {r : _root_.ThreeSum.BandCandidateRows.Record}
    (hr : r ∈ _root_.ThreeSum.BandCandidateRows.records A B C) (hf : r.flag=1) :
    r.a < A.size ∧ r.b < B.size ∧ r.c < C.size ∧
      _root_.ThreeSum.Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (r.a,r.b,r.c) := by
  obtain ⟨o,rfl⟩ := _root_.ThreeSum.BandCandidateRows.mem_records_owner hr
  exact _root_.ThreeSum.BandCandidateRows.fromOwner_sound A B C o hf



theorem getD_sound {A B C : _root_.ThreeSum.BandEnumeration.Family} {s : ℕ} (hs : s < (_root_.ThreeSum.BandCandidateRows.records A B C).length)
    (hf : ((_root_.ThreeSum.BandCandidateRows.records A B C).getD s default).flag=1) :
    let r := (_root_.ThreeSum.BandCandidateRows.records A B C).getD s default
    r.a < A.size ∧ r.b < B.size ∧ r.c < C.size ∧
      _root_.ThreeSum.Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (r.a,r.b,r.c) := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.records_sound _ hf
  rw [List.getD_eq_getElem _ _ hs]
  exact List.getElem_mem hs









end ThreeSum.BandCandidateRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Stable extraction of one color class from the original signed array

The program reads stored colors and original values. It writes a length
header followed by exactly the selected values, optionally negated. Repeated
values are preserved; deduplication belongs to the later normalization pass.
-/

namespace ThreeSum.LightClassFilter
open _root_.ThreeSum.LightClassFilter


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000







theorem items_length_le (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) :
    (_root_.ThreeSum.LightClassFilter.items x color want scale n).length ≤ n := by
  simpa only [_root_.ThreeSum.LightClassFilter.items,List.length_map,List.length_range] using
    List.length_filter_le (p := fun i => decide (color i = want)) (l := List.range n)

theorem mem_items (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) (z : ℤ) :
    z ∈ _root_.ThreeSum.LightClassFilter.items x color want scale n ↔ ∃ i, i < n ∧ color i = want ∧ scale*x i = z := by
  simp [_root_.ThreeSum.LightClassFilter.items,and_assoc]









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







end ThreeSum.LightClassFilter

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retained local-cover tables survive reuse of the returned free region -/

namespace ThreeSum.LightLocalCoverRetention
open _root_.ThreeSum.LightLocalCoverRetention


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata

set_option maxHeartbeats 1000000

theorem base_le_nextFree (base h : ℕ) : base ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.bitPtr
    _root_.ThreeSum.LightCoverGreedy.total
  omega

theorem table_ends_le (base h : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps base h+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*(2*(464*h)) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 base h+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 base h+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr base h+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.candidates base h+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.candidates _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.bitPtr
    _root_.ThreeSum.LightCoverGreedy.total _root_.ThreeSum.LightCoverGreedy.out
  omega











end ThreeSum.LightLocalCoverRetention

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Occurrence-only source-bank indices, with first block most significant -/

namespace ThreeSum.OutputDecodeOccurrenceCode
open _root_.ThreeSum.OutputDecodeOccurrenceCode


open _root_.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding

set_option maxHeartbeats 1500000



theorem last_lt {T M : ℕ} (hT : 0 < T) (hM : 0 < M) (k : ℕ) :
    (k%(T*M))/M < T :=
  (Nat.div_lt_iff_lt_mul hM).mpr (Nat.mod_lt _ (Nat.mul_pos hT hM))

theorem code_lt {T M : ℕ} (hT : 0 < T) (hM : 0 < M) (J k : ℕ) : _root_.ThreeSum.OutputDecodeOccurrenceCode.code T M J k < T^J := by
  induction J generalizing k with
  | zero => simp [_root_.ThreeSum.OutputDecodeOccurrenceCode.code]
  | succ J ih =>
    have hm := Nat.mul_le_mul_left T (show _root_.ThreeSum.OutputDecodeOccurrenceCode.code T M J (k/(T*M))+1 ≤ T^J by exact ih _)
    have hd := _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode.last_lt hT hM k
    simp only [Nat.mul_add,Nat.mul_one] at hm
    rw [_root_.ThreeSum.OutputDecodeOccurrenceCode.code,pow_succ']
    omega





theorem source_code_lt (h J k : ℕ) :
    _root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J k < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h^J :=
  _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode.code_lt (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.schedule_pos h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount_pos h) J k



end ThreeSum.OutputDecodeOccurrenceCode

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









/-! ## Specifications of single routines -/

/-- A list below fr stays where it is if nothing below fr changes. -/
theorem Seg.of_kept {μ μ' : ℕ → ℤ} {a fr : ℕ} {l : List ℤ} (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (hk : _root_.ThreeSum1960614.Machine.Light.Kept μ μ' fr)
    (hle : a + l.length ≤ fr) : _root_.ThreeSum1960614.Machine.Light.Seg μ' a l :=
  h.of_sameOn hk fun i hi => show a + i < fr by omega

/-! ## Tasks and solvers -/





















/-! ## Hosts -/





/-! ## Tasks with a list of parameters -/











end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact A-value incidences of the physical band-owner catalog

Each successful owner contributes only its A band. Labels retain the
physical owner slot and the coordinate in the retained sorted A array.
Equal values and equal triples in different owner slots remain distinct.
-/

namespace ThreeSum.BandRawA
open _root_.ThreeSum.BandRawA


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition

set_option maxHeartbeats 1600000
set_option maxRecDepth 7000













































theorem mem_firstRows {n g i : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record} {l : _root_.ThreeSum.BandRawA.Label} :
    l ∈ _root_.ThreeSum.BandRawA.firstRows n g rs i ↔
      l.owner < i ∧ l ∈ _root_.ThreeSum.BandRawA.row n g l.owner (rs.getD l.owner default) := by
  constructor
  · intro hl
    obtain ⟨owner,ho,hl⟩ := List.mem_flatMap.mp hl
    have he := (_root_.ThreeSum.BandRawA.mem_row.mp hl).2.1
    subst owner
    exact ⟨List.mem_range.mp ho,hl⟩
  · rintro ⟨ho,hl⟩
    exact List.mem_flatMap.mpr ⟨l.owner,List.mem_range.mpr ho,hl⟩

theorem position_lt {n g i : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record} {l : _root_.ThreeSum.BandRawA.Label}
    (hl : l ∈ _root_.ThreeSum.BandRawA.firstRows n g rs i) : l.position < n := by
  have hh := (_root_.ThreeSum.BandRawA.mem_row.mp (_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.mem_firstRows.mp hl).2).2.2.2
  exact hh.trans_le (_root_.ThreeSum.BandPartition.stop_le n g _)













end ThreeSum.BandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact original-position semantics of the constructed color-class lists

The machine keeps repeated values within a class and negates the third
class. The list membership witnesses are original positions. Any binary
width large enough for the indices suffices for the deterministic family.
-/

namespace ThreeSum.ColorClassLists
open _root_.ThreeSum.ColorClassLists


open _root_.ThreeSum.LightClassFilter
open _root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter













theorem length_classList_le {n W : ℕ} (p : _root_.ThreeSum.Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) : (_root_.ThreeSum.ColorClassLists.classList p x c scale).length ≤ n :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter.items_length_le ..













end ThreeSum.ColorClassLists

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The retained cover, output layers, and exact global key array

This bundle is produced by the actual cover/key host and remains valid when
later phases use its computed next free address. In particular the output
index decoder can read the original layer masks without reconstructing them.
-/

namespace ThreeSum.LightCoverKeyData
open _root_.ThreeSum.LightCoverKeyData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000





theorem layer_end_le_header (free h J : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover free h+_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.keyHeader free h J := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.keyHeader _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.scratch
  omega

theorem afterCover_le_keyEnd (free h J : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover free h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd free h J := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.layer_end_le_header free h J
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd
  omega











end ThreeSum.LightCoverKeyData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Physical incidence indices and their exact owner coordinates

An incidence at position `count owner + localA` retains that physical
owner and its sorted A coordinate. Every emitted index has exactly this
form, including equal values emitted by different owners.
-/

namespace ThreeSum.BandRawA
open _root_.ThreeSum.BandRawA


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows

set_option maxHeartbeats 1700000
set_option maxRecDepth 7000



















theorem at_mem {n g k : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record}
    (hk : k < (_root_.ThreeSum.BandRawA.items n g rs).length) : _root_.ThreeSum.BandRawA.labelAt n g rs k ∈ _root_.ThreeSum.BandRawA.items n g rs := by
  rw [_root_.ThreeSum.BandRawA.labelAt,List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

theorem at_bounds {n g k : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record}
    (hk : k < (_root_.ThreeSum.BandRawA.items n g rs).length) :
    (_root_.ThreeSum.BandRawA.labelAt n g rs k).owner < rs.length ∧
      (_root_.ThreeSum.BandRawA.ownerRecord n g rs k).flag=1 ∧
      _root_.ThreeSum.BandPartition.start g (_root_.ThreeSum.BandRawA.ownerRecord n g rs k).a ≤ (_root_.ThreeSum.BandRawA.labelAt n g rs k).position ∧
      (_root_.ThreeSum.BandRawA.labelAt n g rs k).position < _root_.ThreeSum.BandPartition.stop n g (_root_.ThreeSum.BandRawA.ownerRecord n g rs k).a := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.mem_firstRows.mp (_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.at_mem hk)
  have hr := _root_.ThreeSum.BandRawA.mem_row.mp hh.2
  exact ⟨hh.1,hr.1,hr.2.2.1,hr.2.2.2⟩













end ThreeSum.BandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original input to normalized color bands

This fixed program computes index colors, writes the three class arrays and
their headers, then reads those headers into the existing normalization and
owner-table program. All buffers and resource bounds depend on the original
input length, rather than on externally supplied color-class lengths.
-/

namespace ThreeSum.LightColorBands
open _root_.ThreeSum.LightColorBands


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000








theorem class_bounded {n W U : ℕ} (p : _root_.ThreeSum.Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) (hs : |scale| ≤ 1) (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    ∀ z ∈ _root_.ThreeSum.ColorClassLists.classList p x c scale, |z| ≤ (U : ℤ) := by
  intro z hz
  obtain ⟨i,hi,_,rfl⟩ :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter.mem_items (_root_.ThreeSum.ColorClassLists.value x) (_root_.ThreeSum.LightColorIndex.color p) c scale n z).mp hz
  have hv : |_root_.ThreeSum.ColorClassLists.value x i| ≤ (U : ℤ) := by
    simpa only [_root_.ThreeSum.ColorClassLists.value,hi,dite_true] using hx ⟨i,hi⟩
  rw [abs_mul]
  calc
    |scale| * |_root_.ThreeSum.ColorClassLists.value x i| ≤ 1 * (U : ℤ) :=
      mul_le_mul hs hv (abs_nonneg _) (by norm_num)
    _ = (U : ℤ) := one_mul _



variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}













end ThreeSum.LightColorBands

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # A retained header for the complete shared reporting catalog bank -/

namespace ThreeSum.SharedReportingBankHeader
open _root_.ThreeSum.SharedReportingBankHeader


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.SharedReportingBankRows
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows
open _root_.ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData

set_option maxHeartbeats 1900000








theorem records_le_payload (free h J NB NC g : ℕ) :
    _root_.ThreeSum.SharedReportingBankHeader.records free ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload free h J NB NC g := Nat.le_add_right _ _
theorem payload_le_finish (free h J NB NC g : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload free h J NB NC g ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish free h J NB NC g := Nat.le_add_right _ _














end ThreeSum.SharedReportingBankHeader

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Concrete source inputs from the retained normalization and wanted outputs -/

namespace ThreeSum.SourceFiniteInputs
open _root_.ThreeSum.SourceFiniteInputs


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule










theorem prepared_read {μ : ℕ → ℤ} {values endpoints g : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Represents μ values endpoints g hg original L hs) :
    ∀ j < L.length, μ (values+j)=L.getD j 0 := fun j hj => H.1.getD hj 0



theorem prepared_bound {μ : ℕ → ℤ} {values endpoints g U : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Represents μ values endpoints g hg original L hs)
    (hb : ∀ z ∈ original, |z| ≤ (U : ℤ)) :
    ∀ j < L.length, |L.getD j 0| ≤ (U : ℤ) := by
  intro j hj
  rw [List.getD_eq_getElem _ _ hj]
  exact hb _ ((H.2.2.1 _).mp (List.getElem_mem hj))







end ThreeSum.SourceFiniteInputs

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Typed contents of the executed wanted access and scratch records -/

namespace ThreeSum.ReportingHostWantedControls
open _root_.ThreeSum.ReportingHostWantedControls


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout









theorem ofAccess_record (f : ℕ→ℤ) (n g : ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (idx pair bank cover NB NC h J cut occ code srcB srcC report : ℕ) :
    _root_.ThreeSum.ReportingHostWantedControls.record (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls.ofAccess f n g rs idx pair bank cover NB NC h J cut occ code srcB srcC report)=
      _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess.record f n g rs idx pair bank cover NB NC h J cut occ code srcB srcC report := rfl













end ThreeSum.ReportingHostWantedControls

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Finite scale bounds for every shared-bank resource component -/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum.SharedReportingBankHeader
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader

set_option maxHeartbeats 3000000
set_option maxRecDepth 14000














theorem linear_le_magnitude (n : ℕ) : 2048*(_root_.ThreeSum.Scales.inputBits n+1) ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n := by
  have hh : _root_.ThreeSum.Scales.inputBits n+1 ≤ 2^(_root_.ThreeSum.Scales.inputBits n) := Nat.lt_two_pow_self
  calc
    _ ≤ 2048*2^(_root_.ThreeSum.Scales.inputBits n) := Nat.mul_le_mul_left _ hh
    _ = 2^(_root_.ThreeSum.Scales.inputBits n+11) := by rw [pow_add]; norm_num; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)



















end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.ThreeSum.ThreeSumColorBudgets


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000





variable {μ : ℕ → ℤ} {free n : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n → ℤ}
    {A B C : List ℤ} {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

theorem normalized_lengths (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    A.length ≤ n ∧ B.length ≤ n ∧ C.length ≤ n :=
  ⟨H.normalized.2.1.2.1.trans (_root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.length_classList_le color x 0 1),
    H.normalized.2.2.1.2.1.trans (_root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.length_classList_le color x 1 1),
    H.normalized.2.2.2.1.2.1.trans (_root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.length_classList_le color x 2 (-1))⟩

theorem normalized_values {U : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    (∀ j < A.length, |A.getD j 0| ≤ (U : ℤ)) ∧
      (∀ j < B.length, |B.getD j 0| ≤ (U : ℤ)) ∧
      (∀ j < C.length, |C.getD j 0| ≤ (U : ℤ)) :=
  ⟨_root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_bound H.normalized.2.1
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightColorBands.class_bounded color x 0 1 (by norm_num) hx),
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_bound H.normalized.2.2.1
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightColorBands.class_bounded color x 1 1 (by norm_num) hx),
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_bound H.normalized.2.2.2.1
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightColorBands.class_bounded color x 2 (-1) (by norm_num) hx)⟩















open _root_.Filter



end ThreeSum.ThreeSumColorBudgets

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Size-only magnitudes for physical wanted indices

The left index includes the lift and the retained A-incidence position.
The right index selects an original output record, including its occurrence
identity. Neither bound depends on the magnitude of the input integers.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000





theorem wanted_decode_v_eq (n : ℕ) : _root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n=(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^4 := by
  unfold _root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude
  rw [← pow_mul]
  congr 1
  omega









theorem wanted_left_index_le {n N i : ℕ}
    (hN : N ≤ 3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hi : i<3*N) : i≤_root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n := by
  have h9 : 9≤_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n := by have hh := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.linear_le_magnitude n; omega
  have hh : 9*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3 ≤ (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^4 := by
    calc
      _ ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3 := Nat.mul_le_mul_right _ h9
      _ = _ := by ring
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_decode_v_eq]
  omega

theorem wanted_right_index_le {n j : ℕ}
    (hj : j<_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) : j≤_root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_decode_v_eq]
  exact hj.le.trans ((_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.output_count_le_magnitude n).trans
    (Nat.pow_le_pow_right (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.components n).positive (by decide)))





end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact retained addresses for reporting one encoded original color -/

namespace ThreeSum.ThreeSumReportingSetupData
open _root_.ThreeSum.ThreeSumReportingSetupData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData













theorem report_le_counter (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC+9 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.records_le_payload ..).trans
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload_le_finish ..)







end ThreeSum.ThreeSumReportingSetupData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The actual retained inputs of the physical wanted consumer

These are projections and finite bounds for the same normalized witnesses
retained by the selected-color pipeline. Physical A incidences preserve
their owner labels even when their integer values are equal.
-/

namespace ThreeSum.EncodedColorWantedConsumerData
open _root_.ThreeSum.EncodedColorWantedConsumerData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData

set_option maxHeartbeats 2200000
set_option maxRecDepth 16000







variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

theorem raw_stored (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.Stored μ (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).vals
      (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).owners (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.positions free n A B C hsA hsB hsC)
      (fun j => A.getD j 0) (_root_.ThreeSum.BandRawA.items A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC)) :=
  H.normalized.2.2.2.2.2.2

theorem records_stored (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).records (_root_.ThreeSum.BandCandidateRows.cells (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC)) :=
  H.normalized.2.2.2.2.2.1

theorem normalized_read (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    (∀ j<A.length, μ (_root_.ThreeSum.EncodedColorLayout.av free n+j)=A.getD j 0) ∧
      (∀ j<(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).NB,
        μ ((_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).srcB+j)=B.getD j 0) ∧
      (∀ j<(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).NC,
        μ ((_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).srcC+j)=C.getD j 0) :=
  ⟨_root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_read H.normalized.2.1,
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_read H.normalized.2.2.1,
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_read H.normalized.2.2.2.1⟩

theorem normalized_bound {U : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hx : ∀ i, |x i|≤(U : ℤ)) :
    (∀ j<A.length, |A.getD j 0|≤(U : ℤ)) ∧
      (∀ j<(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).NB, |B.getD j 0|≤(U : ℤ)) ∧
      (∀ j<(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).NC, |C.getD j 0|≤(U : ℤ)) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.normalized_values H hx

theorem incidence_length_eq (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).N=
      (_root_.ThreeSum.BandRawA.items A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC)).length :=
  _root_.ThreeSum.BandRawA.values_length ..











theorem incidence_value_bound {U i : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hx : ∀ j, |x j|≤(U : ℤ)) (hi : i<(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).N) :
    |A.getD (_root_.ThreeSum.BandRawA.labelAt A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC) i).position 0|≤(U : ℤ) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.incidence_length_eq] at hi
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.normalized_bound H hx).1 _ (_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.position_lt (_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.at_mem hi))

theorem owner_bands {i : ℕ} (hi : i<(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).N) :
    (_root_.ThreeSum.BandRawA.ownerRecord A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC) i).a<
      _root_.ThreeSum.BandPartition.size A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) ∧
    (_root_.ThreeSum.BandRawA.ownerRecord A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC) i).b<
      _root_.ThreeSum.BandPartition.size (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).NB (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) ∧
    (_root_.ThreeSum.BandRawA.ownerRecord A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC) i).c<
      _root_.ThreeSum.BandPartition.size (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.incidence_length_eq] at hi
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.at_bounds hi
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.getD_sound hb.1 hb.2.1
  exact ⟨hs.1,hs.2.1,hs.2.2.1⟩

end ThreeSum.EncodedColorWantedConsumerData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Relative resources for the complete guarded wanted reporter

All buffer extents are relative to the caller's arbitrary free address.
Retained pointers are bounded individually by that address; they are never
summed into a purported size-only bound. Reserving frontier capacity does
not change the separately verified running time.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout

set_option maxHeartbeats 2600000
set_option maxRecDepth 14000
set_option linter.unusedSectionVars false











theorem wanted_work_eq (dst h J K N NB NC : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout dst h J K N NB NC).work=
      dst+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedWork h J K N NB NC := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedWork _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout _root_.ThreeSum.ReportingHostWantedLayout.make _root_.ThreeSum.ReportingHostFrontierLayout.slot
    _root_.ThreeSum.ReportingHostWantedLayout.root _root_.ThreeSum.ReportingHostWantedLayout.packed _root_.ThreeSum.ReportingHostWantedLayout.access _root_.ThreeSum.ReportingHostWantedLayout.decoded
  ring

theorem wanted_work_formula (h J K N NB NC : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedWork h J K N NB NC=44+3*J+
      (K+1)*(4+2*_root_.ThreeSum.ReportingHostWantedLayout.capacityBound N NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J) (_root_.ThreeSum.LocalCoverBounds.groupSize h))+
      5*_root_.ThreeSum.LocalCoverBounds.groupSize h+12*2^(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J)+5*_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedWork _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout _root_.ThreeSum.ReportingHostWantedLayout.make _root_.ThreeSum.ReportingHostFrontierLayout.slot
    _root_.ThreeSum.ReportingHostWantedLayout.root _root_.ThreeSum.ReportingHostWantedLayout.packed _root_.ThreeSum.ReportingHostWantedLayout.access _root_.ThreeSum.ReportingHostWantedLayout.decoded
  ring













section Raw

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]







end Raw
end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# All persistent wanted-consumer inputs precede the mutable counter

The bounds use the actual packed source and wanted extents. In particular,
the pair-array endpoint is the source-control base, and the occurrence rows
end exactly at the shared source-bank header.
-/

namespace ThreeSum.EncodedColorWantedConsumerData
open _root_.ThreeSum.EncodedColorWantedConsumerData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData

set_option maxHeartbeats 2200000
set_option maxRecDepth 16000



variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}











theorem masks_read (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    ∀ j<(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).layerCount,
      μ ((_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).masks+j)=
        (_root_.ThreeSum.LocalMaskGraph.maskAt (464*(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).h)
          (2*(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).h) j : ℤ) := H.cover.masks

end ThreeSum.EncodedColorWantedConsumerData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Polynomial relative resources for every physical wanted slot -/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout

set_option maxHeartbeats 3200000
set_option maxRecDepth 16000













theorem wanted_cells_le {n K N NB NC : ℕ}
    (hK : K≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (hN : N≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedCells (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K N NB NC (_root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n)≤_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n := by
  have hw := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_work_le hK hN hB hC
  have hn := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_numeric_le hK hN hB hC
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_scratch_le n
  have h9 : (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^9≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h7 : (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^7≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h2 : (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^2≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedCells _root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope
  omega



theorem wanted_words_le {n N : ℕ} (hN : N≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminal.word (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)≤_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.word (_root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n) N (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)≤_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.queryWord (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)≤_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n := by
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_terminal_word_le n
  have hd := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_decoder_word_le hN
  have hq := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.query_word_le n
  have h2 : (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^2≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h4 : (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^4≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h6 : (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^6≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  unfold _root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope _root_.ThreeSum.SharedReportingBankResourceBounds.queryEnvelope at *
  omega



theorem wanted_envelope_positive (n : ℕ) : 2≤_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n := by
  have h1 : 1≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^10 := Nat.one_le_pow _ _ (by omega)
  unfold _root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope
  omega

noncomputable section





theorem wanted_buffers_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {dst n U K N NB NC d : ℕ}
    (hK : K≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (hN : N≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.WantedBuffers lim dst (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K N NB NC (_root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_buffers ((Nat.add_le_add_left (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_cells_le hK hN hB hC) dst).trans hok.cells)

theorem wanted_envelope_word_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {dst n U d : ℕ}
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d) : (_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n : ℤ)≤lim.word :=
  (Int.ofNat_le.mpr (Nat.le_mul_of_pos_right _ (by omega : 0<U+1))).trans hok.word

theorem wanted_values_word_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {dst n U d : ℕ}
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d) : ((2*U : ℕ) : ℤ)≤lim.word := by
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_envelope_positive n
  have hb : 2*U≤_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n*(U+1) :=
    (Nat.mul_le_mul_left 2 (Nat.le_succ _)).trans (Nat.mul_le_mul_right _ he)
  exact (Int.ofNat_le.mpr hb).trans hok.word

theorem wanted_relative_space_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {dst cover counter n U K N NB NC d : ℕ}
    (hK : K≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (hN : N≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hcover : cover+4≤dst) (hcounter : counter+3≤dst)
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.relativeSpace dst cover counter (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K N NB NC≤lim.space := by
  have H := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_buffers_of_ok hK hN hB hC hok
  have hw := H.numeric
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_work_eq dst (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K N NB NC
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNumeric _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.relativeSpace _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.numericExtra at *
  omega

end
end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Retain the selected-color inputs while the wanted counter changes

Only the first dense-header cell is mutable during the scan. The encoded
payload, shared reporting catalog, threshold, cap and original false score
remain available with exactly the same normalized-list witnesses.
-/

namespace ThreeSum.EncodedColorWantedConsumerData
open _root_.ThreeSum.EncodedColorWantedConsumerData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000



variable {μ ν : ℕ→ℤ} {free n : ℕ}
  {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}



theorem retained_of_kept
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (HQ : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.Catalog μ free n A B C hsA hsB hsC)
    (K : _root_.ThreeSum1960614.Machine.Light.Kept μ ν (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter) :
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored ν free n color x A B C hsA hsB hsC ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.Catalog ν free n A B C hsA hsB hsC := by
  have hbefore := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.report_le_counter free n A B C hsA hsB hsC
  have hsource : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC+8≤
      (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter := by
    change _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC≤
      _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC
    omega
  exact ⟨H.of_kept K hsource,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.Stored.of_kept HQ K le_rfl⟩









end ThreeSum.EncodedColorWantedConsumerData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Concrete execution and query resources under the wanted reporter's Need

The actual two-procedure layout constructor runs once and stores the same
fourteen pointers. Every subsequent shared-catalog query uses those pointers
without constructing another catalog or clearing its reserved buffers.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout

set_option maxHeartbeats 2200000
set_option maxRecDepth 13000

theorem wanted_words_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {dst n U N d : ℕ}
    (hN : N≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminal.word (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) : ℤ)≤lim.word ∧
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.word (_root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n) N (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) : ℤ)≤lim.word ∧
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.queryWord (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) : ℤ)≤lim.word := by
  obtain ⟨ht,hd,hq⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_words_le hN
  have hw := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_envelope_word_of_ok hok
  exact ⟨(Int.ofNat_le.mpr ht).trans hw,(Int.ofNat_le.mpr hd).trans hw,(Int.ofNat_le.mpr hq).trans hw⟩





theorem wanted_integer_word_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {dst n U d : ℕ} {z : ℤ}
    (hz : |z|≤(U : ℤ)) (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d) : |z|≤lim.word := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_values_word_of_ok hok
  have hu : (0 : ℤ)≤(U : ℤ) := Int.natCast_nonneg _
  push_cast at hh
  omega



theorem wanted_depth_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {dst n U K N NB NC d : ℕ}
    (hK : K≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (hN : N≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d) :
    d+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedDepth (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K N NB NC≤lim.depth :=
  (Nat.add_le_add_left (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_depth_le hK hN hB hC) d).trans hok.depth



theorem wanted_layout_meets {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ→ℤ} {dst cover counter n U K N NB NC d : ℕ}
    (hK : K≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (hN : N≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hcover : cover+4≤dst) (hcounter : counter+3≤dst)
    (hgroup : μ (cover+3)=(_root_.ThreeSum.LocalCoverBounds.groupSize (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) : ℤ))
    (hcap : μ (counter+2)=(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) : ℤ))
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.program 1 d
      [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n,_root_.ThreeSum.SharedReportingBankResourceBounds.half n,K,cover,counter,N,NB,NC,dst] μ
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.time (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))
      (fun result ν =>
        result=((_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout dst (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K N NB NC).work : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN ν dst (_root_.ThreeSum.ReportingHostWantedLayout.values (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout dst (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K N NB NC)) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν dst 14) := by
  have hd := hok.depth
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_envelope_positive n
  change d+_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n≤lim.depth at hd
  exact _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.program_meets_relative hgroup hcap hok.space (by omega)
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_relative_space_of_ok hK hN hB hC hcover hcounter hok)

end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Every selected persistent row remains before the counter

The bounds keep the selected B and C bands independent. Each incidence and
occurrence is selected by its retained physical label, and every translated
pointer is bounded individually by the already occupied prefix.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.ReportingHostSourceSelection
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored

set_option maxHeartbeats 2800000
set_option maxRecDepth 15000



theorem wanted_cover_ends (cover h J : ℕ) :
    cover+20≤_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd cover h J ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps (_root_.ThreeSum.LightLocalCoverInit.base cover) h+2*(464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h≤
      _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd cover h J ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.candidates (_root_.ThreeSum.LightLocalCoverInit.base cover) h+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h≤
      _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd cover h J ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 (_root_.ThreeSum.LightLocalCoverInit.base cover) h+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h≤
      _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd cover h J ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 (_root_.ThreeSum.LightLocalCoverInit.base cover) h+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h≤
      _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd cover h J := by
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention.base_le_nextFree (_root_.ThreeSum.LightLocalCoverInit.base cover) h
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention.table_ends_le (_root_.ThreeSum.LightLocalCoverInit.base cover) h
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.afterCover_le_keyEnd cover h J
  change _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree (_root_.ThreeSum.LightLocalCoverInit.base cover) h≤_ at he
  refine ⟨hb.trans he,?_,ht.2.2.2.2.trans he,ht.2.1.trans he,ht.2.2.1.trans he⟩
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree,Nat.mul_comm] using he









end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Individual selector bounds from the proved wanted Need -/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum.ReportingHostSourceSelection
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored

set_option maxHeartbeats 2300000
set_option maxRecDepth 14000

theorem WantedSourceEnds.fits {X : _root_.ThreeSum.ReportingHostSourceSelection.Pointers}
    {pair bank cover srcB srcC i j code h J cut stop out limit : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.WantedSourceEnds X pair bank cover srcB srcC i j code h J cut stop)
    (hs : stop≤limit) (hout : out+15≤limit) (hscalar : J+X.bankSpan+20≤limit) :
    _root_.ThreeSum.ReportingHostSourceSelection.Fits X pair bank cover srcB srcC i j code J out limit := by
  refine ⟨H.pairHeader.trans hs,H.bankHeader.trans hs,H.coverHeader.trans hs,hout,
    H.leftHead.trans hs,H.rightHead.trans hs,H.leftCell.trans hs,H.rightCell.trans hs,
    ?_,hscalar,fun v hv => (H.values v hv).trans hs⟩
  exact (Nat.le_add_right _ _).trans (H.occurrence.trans hs)

theorem wanted_selector_scalars_le (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n+_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (_root_.ThreeSum.LightBlockQuery.sourceCut (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))+20≤
      _root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n := by
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.source_span_le_magnitude n
  have hj := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.components n).blocksBound
  have hm : _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^10 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  have h3 : (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^3≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h1 : 1≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^10 := Nat.one_le_pow _ _ (by omega)
  unfold _root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope _root_.ThreeSum.LightBlockQuery.sourceCut
  omega



theorem wanted_access_output_le {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {dst n U K N NB NC d : ℕ}
    (hK : K≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (hN : N≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d) :
    _root_.ThreeSum.ReportingHostWantedLayout.access dst (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)+20≤lim.space := by
  have H := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_buffers_of_ok hK hN hB hC hok
  have hw := H.numeric
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_work_eq dst (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K N NB NC
  have hf := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_work_formula (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K N NB NC
  unfold _root_.ThreeSum.ReportingHostWantedLayout.access _root_.ThreeSum.ReportingHostWantedLayout.decoded
  omega

theorem wanted_source_fits_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
    {pair bank cover srcB srcC NB NC n U occ i j code stop dst out d : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.WantedSourceEnds
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored.retained pair bank cover NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
        (_root_.ThreeSum.LightBlockQuery.sourceCut (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) occ i j code)
      pair bank cover srcB srcC i j code (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
        (_root_.ThreeSum.LightBlockQuery.sourceCut (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) stop)
    (hstop : stop≤dst) (hout : out+15≤lim.space)
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d) :
    _root_.ThreeSum.ReportingHostSourceSelection.Fits
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored.retained pair bank cover NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
        (_root_.ThreeSum.LightBlockQuery.sourceCut (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) occ i j code)
      pair bank cover srcB srcC i j code (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) out lim.space := by
  have he := hok.cells
  have hs : _root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n≤lim.space := by change dst+_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n≤lim.space at he; omega
  exact H.fits (by omega) hout ((_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_selector_scalars_le n).trans hs)

theorem wanted_access_fits_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
    {pair bank cover srcB srcC NB NC n U K N occ i j code stop dst d : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.WantedSourceEnds
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored.retained pair bank cover NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
        (_root_.ThreeSum.LightBlockQuery.sourceCut (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) occ i j code)
      pair bank cover srcB srcC i j code (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
        (_root_.ThreeSum.LightBlockQuery.sourceCut (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) stop)
    (hstop : stop≤dst) (hK : K≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (hN : N≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d) :
    _root_.ThreeSum.ReportingHostSourceSelection.Fits
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored.retained pair bank cover NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
        (_root_.ThreeSum.LightBlockQuery.sourceCut (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) occ i j code)
      pair bank cover srcB srcC i j code (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
      (_root_.ThreeSum.ReportingHostWantedLayout.access dst (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)+5) lim.space :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_source_fits_of_ok H hstop (by have hh := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_access_output_le hK hN hB hC hok; omega) hok

end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Physical labels and original-fiber semantics for the retained consumer -/

namespace ThreeSum.ReportingHostWantedConsumerData
open _root_.ThreeSum.ReportingHostWantedConsumerData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
open _root_.ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum.ReportingHostWantedPhysical
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
open _root_.ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout

set_option maxHeartbeats 2300000
set_option maxRecDepth 16000

theorem cut_eq_mu (n : ℕ) : _root_.ThreeSum.LightBlockQuery.sourceCut (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)=_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
  unfold _root_.ThreeSum.LightBlockQuery.sourceCut _root_.ThreeSum.SharedReportingBankResourceBounds.half _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize _root_.ThreeSum.Scales.microSize _root_.ThreeSum.Scales.microHalf
  ring

theorem depth_le_blocks (n : ℕ) : _root_.ThreeSum.LightSwitchDepth.depth (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n := by
  unfold _root_.ThreeSum.LightSwitchDepth.depth
  omega















variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}















end ThreeSum.ReportingHostWantedConsumerData

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatchStored

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
open _root_.ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum.ReportingHostWantedPhysical
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum.ReportingHostWantedConsumerData
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData
open _root_.ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
set_option maxHeartbeats 3800000
set_option maxRecDepth 24000
set_option linter.unusedSectionVars false
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatchStored.program_meets__implementation_866eae7c03 {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ→ℤ} {free n U d s raw output old threshold : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (HQ : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.Catalog μ free n A B C hsA hsB hsC)
    (hx : ∀ i, |x i|≤(U : ℤ))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.Label n A B C hsA hsB hsC)
    (hs : s<_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)
    (hraw : raw<3*(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).N)
    (hout : output<_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)^_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
    (hpos : w.1.val=raw%(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).N)
    (he : w.2.2=_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeOriginal.output (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) output)
    (hleft : μ ((_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).pairs+2*s)=(raw : ℤ))
    (hright : μ ((_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).pairs+2*s+1)=(output : ℤ))
    (hp : 0<_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (hguard : 4*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)≤_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))
    (hkey : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) ∣
      _root_.ThreeSum.BandRawA.valueAt A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC) (fun j => A.getD j 0) w.1.val %
        (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)+
      _root_.ThreeSum.RawIncidences.lift w.2.1*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)+
      _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.shift n A B C hsA hsB hsC-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2)
    (hcounter : μ (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter=(old : ℤ))
    (hthreshold : μ ((_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter+1)=(threshold : ℤ))
    (hcap : μ ((_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter+2)=(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) : ℤ))
    (hold : old≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^7)
    (hmass : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.labelMass n A B C hsA hsB hsC w≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^7)
    (hthresholdBound : threshold≤9*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^8)
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).layoutHeader (d+1)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatch.program 151 d
      (_root_.ThreeSum.LightReportingWantedDispatch.arguments (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC) s) μ
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatch.time (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC) (_root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n)
        (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.recordTime free n A B C hsA hsB hsC w output old threshold))
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ threshold<old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.labelMass n A B C hsA hsB hsC w ∨ _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.labelHit n A B C hsA hsB hsC w) ∧
        ν (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter=((old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.labelMass n A B C hsA hsB hsC w : ℕ) : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).layoutHeader
          (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter 1) := by
  let cfg := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC
  let rs := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC
  let L := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout cfg.layoutHeader cfg.h cfg.J cfg.K cfg.N cfg.NB cfg.NC
  let occ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.occurrence free n A B C hsA hsB hsC
  let code := _root_.ThreeSum.OutputDecodeOccurrenceCode.code cfg.scheduleSize cfg.layerCount cfg.J output
  let S := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.selected (fun j => A.getD j 0) A.length B.length C.length
    (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) cfg.pair cfg.bank cfg.cover cfg.h cfg.J occ cfg.srcB cfg.srcC cfg.report rs w output
  let Q := fun (r : ℤ) ν => (r=0 ∨ r=1) ∧
    (r=1 ↔ threshold<old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.labelMass n A B C hsA hsB hsC w ∨ _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.labelHit n A B C hsA hsB hsC w) ∧
    ν cfg.counter=((old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.labelMass n A B C hsA hsB hsC w : ℕ) : ℤ) ∧
    _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν cfg.layoutHeader cfg.counter 1
  have hNI : cfg.N=(_root_.ThreeSum.BandRawA.items A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs).length := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.incidence_length_eq ..
  have hNI0 := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.incidence_length_eq free n A B C hsA hsB hsC
  have hL : L=_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout cfg.layoutHeader (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
      (_root_.ThreeSum.LightSwitchDepth.depth (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) (_root_.ThreeSum.BandRawA.items A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs).length B.length C.length := by
    dsimp only [L]
    rw [hNI]
    rfl
  have hSL : S.NL=_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.leftCount rs B.length w := rfl
  have hSR : S.NR=_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.rightCount rs C.length w := rfl
  have hpos' : w.1.val=raw%(_root_.ThreeSum.BandRawA.items A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs).length := hpos.trans (congrArg (raw%·) hNI)
  have hpos0 : w.1.val=raw%(_root_.ThreeSum.BandRawA.items A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC)).length := hpos'
  have hi : w.1.val<cfg.N := by rw [hNI]; exact w.1.isLt
  obtain ⟨_,hiB,hiC⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.owner_bands hi
  have hB := (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.normalized_lengths H).2.1
  have hC := (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.normalized_lengths H).2.2
  have hN : cfg.N≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3 := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.incidence_length_le_magnitude H
  have hN' : (_root_.ThreeSum.BandRawA.items A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs).length≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3 := by rw [← hNI]; exact hN
  have hK : cfg.K≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.depth_le_blocks n
  have hends : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.PersistentEnds cfg (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.positions free n A B C hsA hsB hsC) occ (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)
      rs.length (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC) := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.persistent_ends H
  have hbank : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish cfg.bank B.length C.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
      (_root_.ThreeSum.LightBlockQuery.sourceCut (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))≤cfg.report := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.cut_eq_mu]
    exact hends.bank
  have hreport : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish cfg.report cfg.h cfg.J cfg.NB cfg.NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)≤cfg.counter := hends.report
  have hbefore : cfg.counter+4=cfg.layoutHeader := rfl
  have hc : cfg.counter≤cfg.layoutHeader := by dsimp only [cfg,rs] at *; omega
  have hbuf := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_buffers_of_ok hK hN hB hC hok
  have hdep := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_depth_of_ok hK hN hB hC hok
  have hd50 : d+1+50≤lim.depth :=
    (Nat.add_le_add_left (show 50≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedDepth (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) cfg.K cfg.N B.length C.length from
      Nat.le_add_left 50 _) (d+1)).trans hdep
  have hd : d+5<lim.depth := by dsimp only [cfg,rs] at *; omega
  have haccess : _root_.ThreeSum.ReportingHostWantedLayout.access cfg.layoutHeader cfg.J+20≤lim.space := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_access_output_le hK hN hB hC hok
  have hspace : cfg.layoutHeader+38+2*cfg.J≤lim.space := by
    unfold _root_.ThreeSum.ReportingHostWantedLayout.access _root_.ThreeSum.ReportingHostWantedLayout.decoded at haccess
    dsimp only [cfg,rs] at *; omega
  have hg : cfg.cover+4≤cfg.layoutHeader := by
    have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_cover_ends cfg.cover cfg.h cfg.J).1.trans hends.cover
    dsimp only [cfg,rs] at *; omega
  have hcode : code<_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count cfg.h cfg.J :=
    _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode.source_code_lt cfg.h cfg.J output
  have hselectedEnds := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_selected_ends (occ := occ) (cut := _root_.ThreeSum.LightBlockQuery.sourceCut (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))
    (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hiB hiC hcode hends.srcB hends.srcC hends.pair
    (hbank.trans (by have hb := hends.reportBeforeCounter; dsimp only [cfg,rs] at *; omega)) hends.occurrence hends.cover
  have hfit := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_access_fits_of_ok (N := cfg.N) hselectedEnds hc hK hN hB hC hok
  have hval := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.incidence_value_bound H hx hi
  have hvalWord := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_integer_word_of_ok hval hok
  let AP := fun ν => _root_.ThreeSum1960614.Machine.Light.SegN ν cfg.layoutHeader (_root_.ThreeSum.ReportingHostWantedLayout.values L) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν cfg.layoutHeader
  let BP := fun ν => _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.Stored ν (_root_.ThreeSum.ReportingHostWantedLayout.decoded cfg.layoutHeader)
      (_root_.ThreeSum.BandRawA.items A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs).length cfg.h cfg.J raw output ∧
    _root_.ThreeSum1960614.Machine.Light.Seg ν (_root_.ThreeSum.ReportingHostWantedLayout.access cfg.layoutHeader cfg.J) (_root_.ThreeSum.ReportingHostWantedControls.record S) ∧
    _root_.ThreeSum1960614.Machine.Light.SegN ν cfg.layoutHeader (_root_.ThreeSum.ReportingHostWantedLayout.values L) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν cfg.layoutHeader
  have retained (ν : ℕ→ℤ) (hk : _root_.ThreeSum1960614.Machine.Light.Kept μ ν cfg.layoutHeader) :=
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.retained_of_kept H HQ (fun a ha => hk a (ha.trans_le hc))
  apply _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatch.program_meets (L := L) (A := AP) (B := BP) (Q := Q)
    hok.space (by dsimp only [cfg,rs] at *; omega) hspace
  · have hgRead := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.cover_scalars H.cover).1
    exact (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_layout_meets hK hN hB hC hg (by dsimp only [cfg,rs] at *; omega) hgRead hcap hok).mono le_rfl
      (fun r ν hr => ⟨hr.1,hr.2.1,fun a ha => hr.2.2 a (Or.inl ha)⟩)
  · intro ν hν
    obtain ⟨Hν,HQν⟩ := retained ν hν.2
    have HBν : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.Stored ν (fun j => B.getD j 0) (fun j => C.getD j 0)
        cfg.bank B.length C.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
        (_root_.ThreeSum.LightBlockQuery.sourceCut (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) occ
        (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)
        (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.shift n A B C hsA hsB hsC) := by
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.cut_eq_mu]
      exact Hν.sources.banks
    have hraw' : raw<3*(_root_.ThreeSum.BandRawA.items A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs).length := by rw [← hNI]; exact hraw
    have hiB' : (_root_.ThreeSum.BandRawA.ownerRecord A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs (raw%(_root_.ThreeSum.BandRawA.items A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs).length)).b<
        _root_.ThreeSum.BandPartition.size B.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) := by rw [← hpos']; exact hiB
    have hiC' : (_root_.ThreeSum.BandRawA.ownerRecord A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs (raw%(_root_.ThreeSum.BandRawA.items A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs).length)).c<
        _root_.ThreeSum.BandPartition.size C.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) := by rw [← hpos']; exact hiC
    have hdecode := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDecodeAccess.program_meets_fits (d := d+1)
      (decoded := _root_.ThreeSum.ReportingHostWantedLayout.decoded cfg.layoutHeader) (dst := _root_.ThreeSum.ReportingHostWantedLayout.access cfg.layoutHeader cfg.J) (work := L.work)
      (n := A.length) (g := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (rs := rs) (NB := B.length) (NC := C.length)
      (h := _root_.ThreeSum.SharedReportingBankResourceBounds.half n) (J := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (pair := cfg.pair) (bank := cfg.bank) (cover := cfg.cover)
      (srcB := cfg.srcB) (srcC := cfg.srcC) (report := cfg.report) (occ := occ)
      (pairs := cfg.pairs) (slot := s) (masks := cfg.masks)
      (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.raw_stored Hν) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records_stored Hν) hraw' hout
      (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_left_index_le hN hraw) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_right_index_le hout)
      Hν.sources.buckets HBν Hν.cover HQν hiB' hiC' hok.space (by dsimp only [cfg,rs] at *; omega)
      (by have hh := hends.values; rw [hNI] at hh; unfold _root_.ThreeSum.ReportingHostWantedLayout.decoded; dsimp only [cfg,rs] at *; omega)
      (by have hh := hends.owners; rw [hNI] at hh; unfold _root_.ThreeSum.ReportingHostWantedLayout.decoded; dsimp only [cfg,rs] at *; omega)
      (by have hh := hends.positions; rw [hNI] at hh; unfold _root_.ThreeSum.ReportingHostWantedLayout.decoded; dsimp only [cfg,rs] at *; omega)
      (by have hh := hends.records; unfold _root_.ThreeSum.ReportingHostWantedLayout.decoded; dsimp only [cfg,rs] at *; omega)
      (hends.srcB.trans (by unfold _root_.ThreeSum.ReportingHostWantedLayout.decoded; omega))
      (hends.srcC.trans (by unfold _root_.ThreeSum.ReportingHostWantedLayout.decoded; omega))
      (hends.pair.trans (by unfold _root_.ThreeSum.ReportingHostWantedLayout.decoded; omega))
      (hbank.trans (by have hh := hends.reportBeforeCounter; unfold _root_.ThreeSum.ReportingHostWantedLayout.decoded; omega))
      hends.occurrence (hends.cover.trans (by unfold _root_.ThreeSum.ReportingHostWantedLayout.decoded; omega))
      (hends.report.trans (by unfold _root_.ThreeSum.ReportingHostWantedLayout.decoded; omega))
      (by unfold _root_.ThreeSum.ReportingHostWantedLayout.access; rfl)
      (by have hh := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_work_eq cfg.layoutHeader cfg.h cfg.J cfg.K cfg.N cfg.NB cfg.NC
          have hf := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_work_formula cfg.h cfg.J cfg.K cfg.N cfg.NB cfg.NC
          change _root_.ThreeSum.ReportingHostWantedLayout.access cfg.layoutHeader cfg.J+20≤
            (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout cfg.layoutHeader cfg.h cfg.J cfg.K cfg.N cfg.NB cfg.NC).work
          unfold _root_.ThreeSum.ReportingHostWantedLayout.access _root_.ThreeSum.ReportingHostWantedLayout.decoded
          dsimp only [cfg,rs] at *; omega)
      (by have hh := hends.pairs; unfold _root_.ThreeSum.ReportingHostWantedLayout.decoded; dsimp only [cfg,rs] at *; omega)
      (hends.masks.trans (by unfold _root_.ThreeSum.ReportingHostWantedLayout.decoded; omega))
      ((hν.2 _ (by have hh := hends.pairs; dsimp only [cfg,rs] at *; omega)).trans hleft)
      ((hν.2 _ (by have hh := hends.pairs; dsimp only [cfg,rs] at *; omega)).trans hright)
      (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.masks_read Hν) hbuf.decoder (by simpa only [cfg,rs,hNI0] using (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_words_of_ok hN hok).2.1)
      (by simpa only [code,cfg,rs,_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config,_root_.ThreeSum.SharedReportingBankResourceBounds.half,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess.selection,← hpos0] using hfit)
      (by simpa only [cfg,rs,← hpos0] using hvalWord)
    have hdecode' := hdecode.mono (R' := fun _ ξ => BP ξ) le_rfl (fun _ ξ hr => by
      refine ⟨hr.2.1,?_,?_,?_⟩
      · simpa only [S,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.selected,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls.ofAccess_record,
          cfg,rs,_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config,_root_.ThreeSum.SharedReportingBankResourceBounds.half,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks,← hpos0] using hr.2.2.1
      · exact hν.1.of_kept hr.2.2.2 (by simp only [_root_.ThreeSum.ReportingHostWantedLayout.values,List.length_map,List.length_cons,List.length_nil,_root_.ThreeSum.ReportingHostWantedLayout.decoded]; omega)
      · exact fun a ha => (hr.2.2.2 a (by unfold _root_.ThreeSum.ReportingHostWantedLayout.decoded; dsimp only [cfg,rs] at *; omega)).trans (hν.2 a ha))
    simpa only [_root_.ThreeSum.LightReportingWantedDispatch.decodeArguments,cfg,rs,_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config,_root_.ThreeSum.SharedReportingBankResourceBounds.half,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences,
      _root_.ThreeSum.BandRawA.values_length,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records] using hdecode'
  · intro ν hν
    obtain ⟨Hν,HQν⟩ := retained ν hν.2.2.2
    have HBν : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.Stored ν (fun j => B.getD j 0) (fun j => C.getD j 0)
        cfg.bank B.length C.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
        (_root_.ThreeSum.LightBlockQuery.sourceCut (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) occ
        (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)
        (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.shift n A B C hsA hsB hsC) := by
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.cut_eq_mu]
      exact Hν.sources.banks
    have hrun := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordNeed.program_meets (d := d+1)
      (pair := cfg.pair) (bank := cfg.bank) (cover := cfg.cover) (occ := occ)
      (srcB := cfg.srcB) (srcC := cfg.srcC) (report := cfg.report) (records := cfg.records)
      (dst := cfg.layoutHeader) (counter := cfg.counter) (K := cfg.K) w
      Hν.sources.buckets HBν Hν.cover HQν hiB hiC hout he hp hguard le_rfl hK hkey
      hν.2.1 (by have hh := hν.2.2.1; rw [hL] at hh; exact hh) hν.1 (by omega)
      ((hν.2.2.2 _ (by dsimp only [cfg,rs] at *; omega)).trans hcounter)
      ((hν.2.2.2 _ (by dsimp only [cfg,rs] at *; omega)).trans hthreshold)
      hselectedEnds hends.records hends.srcB hends.srcC hbank hreport hN' hB hC
      hold hmass hthresholdBound (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.normalized_read Hν).2.1 (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.normalized_read Hν).2.2
      (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.normalized_bound H hx).2.1 (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.normalized_bound H hx).2.2 hval hok
    have hrun' := hrun.mono (R' := Q) le_rfl (fun r ξ hr => by
      refine ⟨hr.1,hr.2.1,hr.2.2.1,?_⟩
      intro a ha
      exact (hr.2.2.2 a ⟨by unfold _root_.ThreeSum.ReportingHostWantedLayout.packed _root_.ThreeSum.ReportingHostWantedLayout.access _root_.ThreeSum.ReportingHostWantedLayout.decoded; dsimp only [cfg,rs] at *; omega,ha.2⟩).trans (hν.2.2.2 a ha.1))
    dsimp only [S,cfg,rs,_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config,_root_.ThreeSum.SharedReportingBankResourceBounds.half,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks] at hSL hSR
    simpa only [_root_.ThreeSum.LightReportingWantedDispatch.recordArguments,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.recordTime,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.labelMass,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.labelHit,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.fiber,
      hSL,hSR,cfg,_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config,_root_.ThreeSum.SharedReportingBankResourceBounds.half,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus,_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix,_root_.ThreeSum1960614.Machine.ThreeSum.Scales.localRadix,
      _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.shift] using hrun'
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatchStored.program_meets__implementation_866eae7c03) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatchStored.program_meets__implementation_866eae7c03)

#print axioms solution
