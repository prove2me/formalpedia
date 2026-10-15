-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordNeed.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:00:57.647413+00:00
-- url     : https://prove2.me/submissions/6dcf1636-ced7-4c81-89c7-c29f450f7e9c

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingWantedRecord_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_WantedSourceEnds_values
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_query_scratch
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_query_word_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_buffers
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_decoder_word_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_depth_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_numeric_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_record_space_of_ok
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_scratch_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_terminal_word_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_work_le
import Theorems.Thm_ThreeSum_BandRawA_mem_row

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
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightReportingWantedRecordNeed
end ThreeSum.LightReportingWantedRecordNeed
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
namespace ThreeSum.ReportingHostWantedControls
end ThreeSum.ReportingHostWantedControls
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankAccess
end ThreeSum.SharedReportingBankAccess
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows
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
namespace ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
end ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
end ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordNeed
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordNeed
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
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess
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
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds

namespace ThreeSum1960614.Machine

/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition
open _root_.ThreeSum.BandPartition






theorem size_le (n g : ℕ) : _root_.ThreeSum.BandPartition.size n g ≤ n := by
  unfold _root_.ThreeSum.BandPartition.size
  split_ifs with h
  · omega
  · have hdiv := Nat.div_le_self (n-1) g
    omega

























end ThreeSum.BandPartition

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
# A reusable finite scratch layout for every wanted slot

The capacity uses the original physical input counts and the retained
representation cap. Its memory bound does not charge any traversal time:
only the actual retained frontier cells are visited. A mask span of `2^W`
also bounds every partial-depth terminal candidate array.
-/

namespace ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum.ReportingHostWantedLayout


open _root_.Finset
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false





















theorem make_bounds {root K W G T cap cap' : ℕ} (hc : cap≤cap') :
    _root_.ThreeSum.ReportingHostWantedLayout.Bounds (_root_.ThreeSum.ReportingHostWantedLayout.make root K W G T cap') root K W G T cap := by
  have hf : _root_.ThreeSum.ReportingHostFrontierLayout.slot root cap (K+1)≤_root_.ThreeSum.ReportingHostFrontierLayout.slot root cap' (K+1) :=
    Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
  refine ⟨rfl,hf,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,?_,?_,le_rfl,le_rfl,le_rfl,?_,le_rfl,le_rfl⟩
  · simp only [_root_.ThreeSum.ReportingHostWantedLayout.make]
    omega
  · simp only [_root_.ThreeSum.ReportingHostWantedLayout.make]
    omega
  · rfl





section Mass

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]







end Mass

end ThreeSum.ReportingHostWantedLayout

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















end ThreeSum.BandRawA

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







theorem values_getD {n g k : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record} (f : ℕ → ℤ)
    (hk : k < (_root_.ThreeSum.BandRawA.items n g rs).length) :
    (_root_.ThreeSum.BandRawA.values f (_root_.ThreeSum.BandRawA.items n g rs)).getD k 0=f (_root_.ThreeSum.BandRawA.labelAt n g rs k).position := by
  unfold _root_.ThreeSum.BandRawA.values _root_.ThreeSum.BandRawA.labelAt
  rw [_root_.List.getD_map_of_lt _ hk default 0]





end ThreeSum.BandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact occurrence/B-band/C-band row order and retained catalog ownership -/

namespace ThreeSum.SharedReportingBankRows
open _root_.ThreeSum.SharedReportingBankRows


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData

set_option maxHeartbeats 1800000











theorem rank_lt {S nb nc s i j : ℕ} (hs : s < S) (hi : i < nb) (hj : j < nc) :
    _root_.ThreeSum.SharedReportingBankRows.rank nb nc s i j < _root_.ThreeSum.SharedReportingBankRows.pairs S nb nc := by
  have hx : s*nb+i < S*nb := calc
    _ < s*nb+nb := Nat.add_lt_add_left hi _
    _ = (s+1)*nb := by ring
    _ ≤ S*nb := Nat.mul_le_mul_right nb (by omega)
  calc
    _ < (s*nb+i)*nc+nc := Nat.add_lt_add_left hj _
    _ = (s*nb+i+1)*nc := by ring
    _ ≤ S*nb*nc := Nat.mul_le_mul_right nc (by omega)

























end ThreeSum.SharedReportingBankRows

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









theorem payload_le_finish (free h J NB NC g : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload free h J NB NC g ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish free h J NB NC g := Nat.le_add_right _ _














end ThreeSum.SharedReportingBankHeader

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Constant-time row addresses and original-output reporting interfaces -/

namespace ThreeSum.SharedReportingBankAccess
open _root_.ThreeSum.SharedReportingBankAccess


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
open _root_.ThreeSum.SharedReportingBankRows
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows
open _root_.ThreeSum.SharedReportingBankHeader
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader
open _root_.ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000








theorem record_end {free h J NB NC g s i j : ℕ}
    (hs : s < _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (hi : i < _root_.ThreeSum.BandPartition.size NB g)
    (hj : j < _root_.ThreeSum.BandPartition.size NC g) :
    _root_.ThreeSum.SharedReportingBankAccess.recordAt free J NB NC g s i j+5*_root_.ThreeSum.SharedReportingBankHeader.levels J ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload free h J NB NC g := by
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rank_lt hs hi hj
  have hh := Nat.mul_le_mul_left (5*_root_.ThreeSum.SharedReportingBankHeader.levels J) (show
    _root_.ThreeSum.SharedReportingBankRows.rank (_root_.ThreeSum.BandPartition.size NB g) (_root_.ThreeSum.BandPartition.size NC g) s i j+1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total h J NB NC g by exact hr)
  unfold _root_.ThreeSum.SharedReportingBankAccess.recordAt _root_.ThreeSum.SharedReportingBankAccess.slot _root_.ThreeSum.SharedReportingBankRows.rowRecord _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload
  nlinarith











end ThreeSum.SharedReportingBankAccess

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



theorem input_le_magnitude (n : ℕ) : n ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n := by
  have hn : n ≤ 2^(_root_.ThreeSum.Scales.inputBits n+1) := by
    simpa only [_root_.ThreeSum.Scales.inputBits,Nat.log2_eq_log_two,Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by decide : 1<2) n).le
  exact hn.trans (Nat.pow_le_pow_right (by decide) (by omega))



















end ThreeSum.SharedReportingBankResourceBounds

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





theorem wanted_power_le (n e f : ℕ) (hef : e≤f) :
    (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^e≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^f :=
  (Nat.pow_le_pow_left (Nat.le_succ _) e).trans (Nat.pow_le_pow_right (by omega) hef)







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



end
end ThreeSum.SharedReportingBankResourceBounds

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



theorem wanted_count_word_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {dst n U NB NC d : ℕ}
    (hB : NB≤n) (hC : NC≤n) (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d) :
    ((NB*NC : ℕ) : ℤ)≤lim.word := by
  have hh := Nat.mul_le_mul (hB.trans (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.input_le_magnitude n)) (hC.trans (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.input_le_magnitude n))
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_power_le n 2 10 (by decide)
  have he : NB*NC≤_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n := by
    simp only [pow_two] at hp
    unfold _root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope
    omega
  exact (Int.ofNat_le.mpr he).trans (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_envelope_word_of_ok hok)

theorem wanted_integer_word_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {dst n U d : ℕ} {z : ℤ}
    (hz : |z|≤(U : ℤ)) (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d) : |z|≤lim.word := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_values_word_of_ok hok
  have hu : (0 : ℤ)≤(U : ℤ) := Int.natCast_nonneg _
  push_cast at hh
  omega

theorem wanted_sum_word_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {dst n U d : ℕ} {a b : ℤ}
    (ha : |a|≤(U : ℤ)) (hb : |b|≤(U : ℤ))
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d) : |a+b|≤lim.word := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_values_word_of_ok hok
  have hs := abs_add_le a b
  push_cast at hh
  omega

theorem wanted_depth_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {dst n U K N NB NC d : ℕ}
    (hK : K≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (hN : N≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d) :
    d+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedDepth (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K N NB NC≤lim.depth :=
  (Nat.add_le_add_left (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_depth_le hK hN hB hC) d).trans hok.depth

theorem wanted_query_scratch_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {dst n U K N NB NC report s i j k d : ℕ}
    (hK : K≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (hN : N≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hk : k≤_root_.ThreeSum.LightSwitchDepth.depth (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Scratch lim (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) k
      (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.levelCatalog report (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
        NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) s i j k)
      (_root_.ThreeSum.BandRawA.finiteBandPositions NB (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) i).card
      (_root_.ThreeSum.BandRawA.finiteBandPositions NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) j).card
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout dst (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K N NB NC).maskBase
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout dst (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K N NB NC).work := by
  have H := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_buffers_of_ok hK hN hB hC hok
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout.make_bounds (root := _root_.ThreeSum.ReportingHostWantedLayout.root dst (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))
    (K := K) (W := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) (G := _root_.ThreeSum.LocalCoverBounds.groupSize (_root_.ThreeSum.SharedReportingBankResourceBounds.half n))
    (T := 2^(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)))
    (cap := _root_.ThreeSum.ReportingHostWantedLayout.capacityBound N NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) (_root_.ThreeSum.LocalCoverBounds.groupSize (_root_.ThreeSum.SharedReportingBankResourceBounds.half n))) le_rfl
  have hmasks : (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout dst (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K N NB NC).maskBase+
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.queryMaskSpan (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)≤
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout dst (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K N NB NC).work := hl.queryMasks
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.query_scratch hk hmasks H.query (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_words_of_ok hN hok).2.2



end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Word bounds for every physical scan prefix, including later prefixes -/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

theorem wanted_guard_word_of_mass_bound {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {dst n U old mass threshold d : ℕ}
    (hold : old≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^7) (hmass : mass≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^7)
    (hthreshold : threshold≤9*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^8)
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d) :
    ((old+mass+threshold+2 : ℕ) : ℤ)≤lim.word := by
  have h7 := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_power_le n 7 10 (by decide)
  have h8 := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_power_le n 8 10 (by decide)
  have h1 : 1≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^10 := Nat.one_le_pow _ _ (by omega)
  have hh : old+mass+threshold+2≤_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n := by
    unfold _root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope
    omega
  exact (Int.ofNat_le.mpr hh).trans (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_envelope_word_of_ok hok)

end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # All twenty selected reporter values fit the actual word limit -/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.ReportingHostWantedControls
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls
open _root_.ThreeSum.ReportingHostSourceSelection
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection

set_option maxHeartbeats 300000
set_option maxRecDepth 14000

theorem wanted_record_values_word {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {f : ℕ→ℤ}
    {n g idx pair bank cover NB NC h J cut occ code srcB srcC report stop : ℕ}
    {rs : List _root_.ThreeSum.BandCandidateRows.Record}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.WantedSourceEnds
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess.selection n g rs idx pair bank cover NB NC h J cut occ code)
      pair bank cover srcB srcC (_root_.ThreeSum.BandRawA.ownerRecord n g rs idx).b (_root_.ThreeSum.BandRawA.ownerRecord n g rs idx).c
      code h J cut stop)
    (hstop : stop≤lim.space) (hw : (lim.space : ℤ)≤lim.word)
    (hav : |f (_root_.ThreeSum.BandRawA.labelAt n g rs idx).position|≤lim.word)
    (ho : (_root_.ThreeSum.BandRawA.labelAt n g rs idx).owner≤lim.space)
    (hb : (_root_.ThreeSum.BandRawA.ownerRecord n g rs idx).b≤lim.space)
    (hc : (_root_.ThreeSum.BandRawA.ownerRecord n g rs idx).c≤lim.space)
    (hcat : _root_.ThreeSum.LightReportingWantedAccess.catalog n g rs idx report J NB NC code≤lim.space) :
    ∀ z∈_root_.ThreeSum.ReportingHostWantedControls.record
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls.ofAccess f n g rs idx pair bank cover NB NC h J cut occ code srcB srcC report), |z|≤lim.word := by
  have hnat (v : ℕ) (hv : v≤lim.space) : |(v : ℤ)|≤lim.word := by
    simpa using (Int.ofNat_le.mpr hv).trans hw
  intro z hz
  simp only [_root_.ThreeSum.ReportingHostWantedControls.record,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls.ofAccess,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact hav
  · exact hnat _ ho
  · exact hnat _ hb
  · exact hnat _ hc
  · exact hnat _ hcat
  all_goals
    apply hnat
    exact (H.values _ (by simp [_root_.ThreeSum.ReportingHostSourceSelection.values])).trans hstop

theorem wanted_record_values_of_allocation {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {f : ℕ→ℤ}
    {n g records idx pair bank cover NB NC h J cut occ code srcB srcC report stop : ℕ}
    {rs : List _root_.ThreeSum.BandCandidateRows.Record}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.WantedSourceEnds
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess.selection n g rs idx pair bank cover NB NC h J cut occ code)
      pair bank cover srcB srcC (_root_.ThreeSum.BandRawA.ownerRecord n g rs idx).b (_root_.ThreeSum.BandRawA.ownerRecord n g rs idx).c
      code h J cut stop)
    (hidx : idx<(_root_.ThreeSum.BandRawA.items n g rs).length)
    (hi : (_root_.ThreeSum.BandRawA.ownerRecord n g rs idx).b<_root_.ThreeSum.BandPartition.size NB g)
    (hj : (_root_.ThreeSum.BandRawA.ownerRecord n g rs idx).c<_root_.ThreeSum.BandPartition.size NC g)
    (hk : code<_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J)
    (hrecords : records+4*rs.length≤ stop) (hsrcB : srcB+NB≤ stop) (hsrcC : srcC+NC≤ stop)
    (hreport : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish report h J NB NC g≤ stop)
    (hstop : stop≤lim.space) (hw : (lim.space : ℤ)≤lim.word)
    (hav : |f (_root_.ThreeSum.BandRawA.labelAt n g rs idx).position|≤lim.word) :
    ∀ z∈_root_.ThreeSum.ReportingHostWantedControls.record
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls.ofAccess f n g rs idx pair bank cover NB NC h J cut occ code srcB srcC report), |z|≤lim.word := by
  have ho := (_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.at_bounds hidx).1
  have hb := hi.trans_le (_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le NB g)
  have hc := hj.trans_le (_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le NC g)
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.record_end (free := report) (J := J) hk hi hj
  have hf := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload_le_finish report h J NB NC g
  apply _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_record_values_word H hstop hw hav (by omega) (by omega) (by omega)
  unfold _root_.ThreeSum.LightReportingWantedAccess.catalog
  omega

end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordNeed

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.BlockMaskLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum.ReportingHostWantedControls
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData
open _root_.ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
set_option linter.unusedSectionVars false
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordNeed.program_meets__implementation_f7bf51a679 {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ}
    {n U NA NB NC pair bank cover p occ srcB srcC records report output dst counter K old threshold d i : ℕ}
    {rs : List _root_.ThreeSum.BandCandidateRows.Record} {shift : ℤ}
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (_root_.ThreeSum.ReportingHostWantedOriginal.AType NA (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs))
    (HP : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.Stored μ fB fC pair NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) shift)
    (HB : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.Stored μ fB fC bank NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
      (_root_.ThreeSum.LightBlockQuery.sourceCut (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) occ (p : ℤ) shift)
    (HC : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.Stored μ cover (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))
    (HQ : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.Stored μ report (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) NB NC
      (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) fB fC (p : ℤ) shift)
    (hi : (_root_.ThreeSum.BandRawA.ownerRecord NA (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs w.1.val).b<_root_.ThreeSum.BandPartition.size NB (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n))
    (hj : (_root_.ThreeSum.BandRawA.ownerRecord NA (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs w.1.val).c<_root_.ThreeSum.BandPartition.size NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n))
    (houtput : output<_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)^_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
    (he : w.2.2=_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeOriginal.output (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) output)
    (hp : 0<p) (hguard : 4*(p : ℤ)≤_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))
    (hK : K≤_root_.ThreeSum.LightSwitchDepth.depth (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) (hKJ : K≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
    (hkey : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)∣ _root_.ThreeSum.BandRawA.valueAt NA (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs fA w.1.val%(p : ℤ)+
      _root_.ThreeSum.RawIncidences.lift w.2.1*(p : ℤ)+shift-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2)
    (hselected : _root_.ThreeSum1960614.Machine.Light.Seg μ (_root_.ThreeSum.ReportingHostWantedLayout.access dst (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))
      (_root_.ThreeSum.ReportingHostWantedControls.record (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.selected fA NA NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) pair bank cover (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
        occ srcB srcC report rs w output)))
    (hlayout : _root_.ThreeSum1960614.Machine.Light.SegN μ dst (_root_.ThreeSum.ReportingHostWantedLayout.values (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout dst (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) K
      (_root_.ThreeSum.BandRawA.items NA (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs).length NB NC)))
    (hdecoded : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.Stored μ (_root_.ThreeSum.ReportingHostWantedLayout.decoded dst)
      (_root_.ThreeSum.BandRawA.items NA (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs).length (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) i output)
    (hcounter : counter+4≤dst)
    (hcounterRead : μ counter=(old : ℤ)) (hthresholdRead : μ (counter+1)=(threshold : ℤ))
    (hends : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.WantedSourceEnds
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess.selection NA (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs w.1.val pair bank cover NB NC
        (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (_root_.ThreeSum.LightBlockQuery.sourceCut (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) occ
        (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) output))
      pair bank cover srcB srcC (_root_.ThreeSum.BandRawA.ownerRecord NA (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs w.1.val).b
      (_root_.ThreeSum.BandRawA.ownerRecord NA (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs w.1.val).c
      (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) output)
      (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (_root_.ThreeSum.LightBlockQuery.sourceCut (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) counter)
    (hrecords : records+4*rs.length≤counter) (hsrcB : srcB+NB≤counter) (hsrcC : srcC+NC≤counter)
    (hbank : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish bank NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
      (_root_.ThreeSum.LightBlockQuery.sourceCut (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))≤report)
    (hreport : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish report (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)≤counter)
    (hN : (_root_.ThreeSum.BandRawA.items NA (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs).length≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3)
    (hB : NB≤n) (hC : NC≤n)
    (hold : old≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^7)
    (hmass : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.localItems (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) NA NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p rs fA fB fC shift w) w≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^7)
    (hthreshold : threshold≤9*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^8)
    (hreadB : ∀ j<NB, μ (srcB+j)=fB j) (hreadC : ∀ j<NC, μ (srcC+j)=fC j)
    (hvaluesB : ∀ j<NB, |fB j|≤(U : ℤ)) (hvaluesC : ∀ j<NC, |fC j|≤(U : ℤ))
    (hvalue : |fA (_root_.ThreeSum.BandRawA.labelAt NA (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs w.1.val).position|≤(U : ℤ))
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d) :
    let S := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.selected fA NA NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) pair bank cover (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
      occ srcB srcC report rs w output
    let D := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.catalogs NA NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) report (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) rs w output
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall.program 138 d
      [_root_.ThreeSum.ReportingHostWantedLayout.access dst (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n),dst,_root_.ThreeSum.SharedReportingBankResourceBounds.half n,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n,K,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n),cover,counter] μ
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWanted.time p shift (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.left rs fB w) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.right rs fC w) S.NL S.NR old threshold
        (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.localItems (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) NA NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p rs fA fB fC shift w) w D K+4000)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ threshold<old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass
          (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.localItems (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) NA NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p rs fA fB fC shift w) w ∨
          _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.Terminal (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) NA NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p rs fA fB fC shift w K) ∧
        ν counter=((old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass
          (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.localItems (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) NA NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) p rs fA fB fC shift w) w : ℕ) : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν (_root_.ThreeSum.ReportingHostWantedLayout.packed dst (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) counter 1) := by
  have hs : counter≤lim.space := by have hh := hok.cells; omega
  have hc : cover+8≤dst := by have hh := hends.coverHeader; omega
  have hav := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_integer_word_of_ok hvalue hok
  have hva : |_root_.ThreeSum.BandRawA.valueAt NA (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) rs fA w.1.val|≤(U : ℤ) := by
    simpa only [_root_.ThreeSum.BandRawA.valueAt,_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.values_getD fA w.1.isLt] using hvalue
  have hw := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_record_values_of_allocation hends w.1.isLt hi hj
    (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode.source_code_lt (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) output)
    hrecords hsrcB hsrcC hreport hs hok.space hav
  exact _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecord.program_meets w HP HB HC HQ hi hj houtput he
    (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hp hguard hK hKJ hkey hselected hlayout hdecoded
    hcounter hcounterRead hthresholdRead hends hbank hreport
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_buffers_of_ok hKJ hN hB hC hok)
    (fun k hk => _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_query_scratch_of_ok hKJ hN hB hC (hk.trans hK) hok)
    hok.space (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_record_space_of_ok hKJ hN hB hC hc (by omega) hok) hw
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_guard_word_of_mass_bound hold hmass hthreshold hok) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_words_of_ok hN hok).1
    hreadB hreadC (fun j hj' => _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_integer_word_of_ok (hvaluesB j hj') hok)
    (fun j hj' => _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_integer_word_of_ok (hvaluesC j hj') hok)
    (fun j hj' => _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_sum_word_of_ok hva (hvaluesB j hj') hok)
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_count_word_of_ok hB hC hok) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_depth_of_ok hKJ hN hB hC hok)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordNeed.program_meets__implementation_f7bf51a679) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordNeed.program_meets__implementation_f7bf51a679)

#print axioms solution
