-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecord.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:05:15.993655+00:00
-- url     : https://prove2.me/submissions/d1bc778f-baf0-444f-8fd7-508c1f94e4ec

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingWantedRecordCall_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingWanted_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_OutputDecodeRecords_global_record_block
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_OutputDecodeRecords_localRecords_getD
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_RawReporting_partitionWord_length
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_RawReporting_word_children
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_ReportingHostMasks_localChildren_mem
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_ReportingHostWantedRecordData_cover_scalars
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankSources_source_bounds
import Theorems.Thm_ThreeSum_BandRawA_mem_aIndices_iff_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_row
import Theorems.Thm_ThreeSum_LocalHashMoments_hitCount_cap
import Theorems.Thm_ThreeSum_Radix_representations_card_le
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_localRow
import Theorems.Thm_ThreeSum_Reporting_frontier_length_le_mass

local instance platformRadixNonzero_3144c44e93 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.Arithmetic
end ThreeSum.Arithmetic
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
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.BlockSourceCoverInput
end ThreeSum.BlockSourceCoverInput
namespace ThreeSum.BlockSourceFlags
end ThreeSum.BlockSourceFlags
namespace ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum.BlockSourceSharing
end ThreeSum.BlockSourceSharing
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightBlockSourceBatch
end ThreeSum.LightBlockSourceBatch
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LightBlockSourceCatalog
end ThreeSum.LightBlockSourceCatalog
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightReportingWantedRecord
end ThreeSum.LightReportingWantedRecord
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.OneHotMask
end ThreeSum.OneHotMask
namespace ThreeSum.OutputDecodeOccurrenceCode
end ThreeSum.OutputDecodeOccurrenceCode
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostFrontier
end ThreeSum.ReportingHostFrontier
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostSourceSelection
end ThreeSum.ReportingHostSourceSelection
namespace ThreeSum.ReportingHostSourceSelectionStored
end ThreeSum.ReportingHostSourceSelectionStored
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.ReportingHostWantedControls
end ThreeSum.ReportingHostWantedControls
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum.ReportingHostWantedPhysical
end ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum.ReportingHostWantedRecordData
end ThreeSum.ReportingHostWantedRecordData
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankAccess
end ThreeSum.SharedReportingBankAccess
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
namespace ThreeSum.SharedReportingBankSources
end ThreeSum.SharedReportingBankSources
namespace ThreeSum.SourceBandBankData
end ThreeSum.SourceBandBankData
namespace ThreeSum.SourceBandBankLayout
end ThreeSum.SourceBandBankLayout
namespace ThreeSum.SourceBandFinite
end ThreeSum.SourceBandFinite
namespace ThreeSum.SourceBandLayout
end ThreeSum.SourceBandLayout
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.Arithmetic
end ThreeSum1960614.Machine.ThreeSum.Arithmetic
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
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
end ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceCoverInput
end ThreeSum1960614.Machine.ThreeSum.BlockSourceCoverInput
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags
end ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
end ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecord
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecord
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.OneHotMask
end ThreeSum1960614.Machine.ThreeSum.OneHotMask
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
namespace ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
end ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
namespace ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
end ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
end ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
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
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandBankData
end ThreeSum1960614.Machine.ThreeSum.SourceBandBankData
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
end ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandFinite
end ThreeSum1960614.Machine.ThreeSum.SourceBandFinite
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
end ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales

namespace ThreeSum1960614.Machine

/-!
# Exact arithmetic interface for the deterministic histogram construction

These are finite arithmetic and counting theorems.  They do not assert a
running-time bound or the existence of a word-RAM implementation.
-/

namespace ThreeSum.Arithmetic
open _root_.ThreeSum.Arithmetic


open _root_.Finset
open scoped _root_.BigOperators

/-! ## Guarded arithmetic-to-radix lifts -/

/-- A multiple of a positive modulus strictly between its two nearest
nonzero multiples must vanish. -/
theorem eq_zero_of_dvd_of_bounds {R x : ℤ} (hR : 0 < R)
    (hlo : -R < x) (hhi : x < R) (hdiv : R ∣ x) : x = 0 := by
  obtain ⟨q, rfl⟩ := hdiv
  by_cases hq : q = 0
  · simp [hq]
  have hcases : q ≤ -1 ∨ 1 ≤ q := by omega
  rcases hcases with hq | hq
  · have hm := mul_le_mul_of_nonneg_left hq hR.le
    nlinarith
  · have hm := mul_le_mul_of_nonneg_left hq hR.le
    nlinarith







/-- Distinct signed lifts of a fixed A residue never give the same radix
query key under the range guard. -/
theorem guarded_lift_unique {P R a d j k : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ R)
    (hj : _root_.ThreeSum.Arithmetic.SmallLift j) (hk : _root_.ThreeSum.Arithmetic.SmallLift k)
    (hcong : R ∣ (a + j * P + d) - (a + k * P + d)) : j = k := by
  have hR : 0 < R := by omega
  have hdiv : R ∣ (j - k) * P := by
    convert hcong using 1 <;> ring
  have hbds : -R < (j - k) * P ∧ (j - k) * P < R := by
    rcases hj with rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl <;> constructor <;> nlinarith
  have hz := _root_.ThreeSum1960614.Machine.ThreeSum.Arithmetic.eq_zero_of_dvd_of_bounds hR hbds.1 hbds.2 hdiv
  rcases mul_eq_zero.mp hz with h | h
  · omega
  · omega







/-! ## The weighted false-count identity -/



























/-! ## Exact early YES from per-original-triple representation caps -/







end ThreeSum.Arithmetic

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition
open _root_.ThreeSum.BandPartition




















theorem length_le (n g i : ℕ) : _root_.ThreeSum.BandPartition.stop n g i-_root_.ThreeSum.BandPartition.start g i ≤ g := by
  have hle : _root_.ThreeSum.BandPartition.stop n g i ≤ (i+1)*g := min_le_right _ _
  unfold _root_.ThreeSum.BandPartition.start
  simp only [Nat.add_mul,Nat.one_mul] at hle
  omega











end ThreeSum.BandPartition

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual local one-hot covers

This module instantiates the hash moment and separable trimming proofs with
the disjoint-subset graph. The sample space consists of all assignments to
the two actual symbols at every coordinate. The resulting deterministic
greedy schedule covers every ordered field target, including equal targets.
-/

namespace ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalHashMoments


open _root_.Finset
open scoped _root_.BigOperators

open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {L h : ℕ}















































/-! ## The selected local prime and its actual finite schedule -/

















theorem local_representation_cap (h : ℕ) (w : _root_.ThreeSum.LocalHashMoments.Weight (464 * h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h))
    (target : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h × _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) :
    _root_.ThreeSum.LocalHashMoments.hitCount (464 * h) h (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h) w target ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h ^ 2 :=
  _root_.ThreeSum.LocalHashMoments.hitCount_cap _ _ _



end ThreeSum.LocalHashMoments

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Query-coordinate lists and weighted subset semantics

The coordinate list has one entry per set bit of the query. Its powers
form a compact weight table for the output-sensitive enumeration routine.
-/

namespace ThreeSum.QueryCoordinates
open _root_.ThreeSum.QueryCoordinates


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators





































theorem setLayer_nodup (xs : List ℕ) (hn : xs.Nodup) (k : ℕ) :
    (_root_.ThreeSum.QueryCoordinates.setLayer xs k).Nodup := by
  apply (List.nodup_sublistsLen k hn).map_on
  intro a ha b hb he
  have ha' := (List.mem_sublistsLen.mp ha).1
  have hb' := (List.mem_sublistsLen.mp hb).1
  apply (hn.perm_iff_eq_of_sublist ha' hb').mp
  exact List.perm_of_nodup_nodup_toFinset_eq (hn.sublist ha') (hn.sublist hb') he



















theorem missingSets_nodup {W : ℕ} (Q : Finset (Fin W)) (k : ℕ) :
    (_root_.ThreeSum.QueryCoordinates.missingSets Q k).Nodup := by
  unfold _root_.ThreeSum.QueryCoordinates.missingSets
  apply (_root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.setLayer_nodup _ (List.nodup_reverse.mpr (_root_.ThreeSum.QueryCoordinates.positions_nodup Q W)) k).map_on
  intro a ha b hb he
  have has := (_root_.ThreeSum.QueryCoordinates.mem_setLayer _ (List.nodup_reverse.mpr (_root_.ThreeSum.QueryCoordinates.positions_nodup Q W)) _ _).mp ha
  have hbs := (_root_.ThreeSum.QueryCoordinates.mem_setLayer _ (List.nodup_reverse.mpr (_root_.ThreeSum.QueryCoordinates.positions_nodup Q W)) _ _).mp hb
  rw [List.toFinset_reverse,_root_.ThreeSum.QueryCoordinates.positions_toFinset] at has hbs
  have h := congrArg _root_.ThreeSum.SubsetAddress.natPositions he
  rw [_root_.ThreeSum.QueryCoordinates.decode_maskOf (has.1.trans (_root_.ThreeSum.SubsetAddress.natPositions_subset Q)),
      _root_.ThreeSum.QueryCoordinates.decode_maskOf (hbs.1.trans (_root_.ThreeSum.SubsetAddress.natPositions_subset Q))] at h
  exact h





end ThreeSum.QueryCoordinates

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Concrete retained choices and the global radix encoding

The local choice type retains the occurrence of a map in the deterministic
schedule.  Repeated chosen maps therefore keep their representation
multiplicity.  Canonical integer lifts of their one-hot coefficients feed
the radix recursion, whose coverage and cap are instantiated here with no
local-cover assumptions.
-/

namespace ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalEncoding


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments






















theorem retained_survives {h : ℕ} (c : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h) :
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Survives h (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence c) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge c) := c.property



theorem rawHash_cast {h L : ℕ} (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (s : Fin L → Bool) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash w s : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) = _root_.ThreeSum.HashFamily.hashValue w s := by
  simp [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash, _root_.ThreeSum.HashFamily.hashValue]





theorem dvd_sub_rawHash_iff {h L : ℕ} (a : ℤ)
    (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (s : Fin L → Bool) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ) ∣ a - _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash w s ↔
      _root_.ThreeSum.HashFamily.hashValue w s = (a : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash_cast, sub_eq_zero]
  exact eq_comm





theorem mem_localFiber {h : ℕ} (a b : ℤ) (c : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h) :
    c ∈ _root_.ThreeSum.Radix.localFiber (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight a b ↔
      _root_.ThreeSum.HashFamily.hashValue (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence c)) (_root_.ThreeSum.LocalGraph.left (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge c)) = (a : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) ∧
      _root_.ThreeSum.HashFamily.hashValue (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence c)) (_root_.ThreeSum.LocalGraph.right (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge c)) = (b : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) := by
  simp only [_root_.ThreeSum.Radix.localFiber, Finset.mem_filter, Finset.mem_univ, true_and,
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.dvd_sub_rawHash_iff]



section

set_option maxHeartbeats 1000000 in
private theorem private_6c1c69abb9_occurrence_fiber_bound (h : ℕ) (a b : ℤ) (i : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h) :
    ((_root_.ThreeSum.Radix.localFiber (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight a b : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h)).filter
      (fun c => _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence c = i)).card ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h ^ 2 := by
  let hits : Finset (_root_.ThreeSum.LocalGraph.Edge (464 * h) h) := Finset.univ.filter fun e =>
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h i ∈ _root_.ThreeSum.HashFamily.trimmedPairEvent (_root_.ThreeSum.LocalGraph.left e) (_root_.ThreeSum.LocalGraph.right e)
      (a : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) (b : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)
      (_root_.ThreeSum.LocalGraph.leftVertices (464 * h) h) (_root_.ThreeSum.LocalGraph.rightVertices (464 * h) h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h)
  have hcount : ((_root_.ThreeSum.Radix.localFiber (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight a b :
      Finset (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h)).filter (fun c => _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence c = i)).card ≤ hits.card := by
    apply Finset.card_le_card_of_injOn _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge
    · intro c hc
      obtain ⟨hc, hi⟩ := Finset.mem_filter.mp hc
      obtain ⟨ha, hb⟩ := (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mem_localFiber a b c).mp hc
      simp only [hi] at ha hb
      have hs := _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.retained_survives c
      simp only [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Survives, hi, ha, hb] at hs
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, hs⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by simpa only [hi] using And.intro ha hb⟩
    · intro c hc d hd he
      apply Subtype.ext
      apply Prod.ext
      · exact (Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hd).2.symm
      · exact he
  exact hcount.trans (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.local_representation_cap h (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h i) (a, b))
end


/-- The exact local cap counts map occurrences separately, including
repetitions in the chosen greedy schedule. -/
theorem localFiber_card_bound (h : ℕ) (a b : ℤ) :
    (_root_.ThreeSum.Radix.localFiber (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight a b : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h)).card ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h * _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h ^ 2 := by
  calc
    _ = ∑ i : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h,
        ((_root_.ThreeSum.Radix.localFiber (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight a b : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h)).filter
          (fun c => _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence c = i)).card := by
      exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ _i : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h, _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.private_6c1c69abb9_occurrence_fiber_bound h a b i
    _ = _ := by simp [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence]











theorem representations_card_bound (h J : ℕ) (a b : ℤ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representations h J a b).card ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J :=
  _root_.ThreeSum.Radix.representations_card_le (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight
    (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h * _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h ^ 2) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.localFiber_card_bound h) J a b



































end ThreeSum.GlobalEncoding

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Packed original-band histograms and exact physical residue fibers -/

namespace ThreeSum.SourceBandLayout
open _root_.ThreeSum.SourceBandLayout


open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets












theorem len_le_cap (n g i : ℕ) : _root_.ThreeSum.SourceBandLayout.len n g i ≤ _root_.ThreeSum.SourceBandLayout.cap n g := by
  have hn := _root_.ThreeSum.BandPartition.stop_le n g i
  have hg := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.length_le n g i
  unfold _root_.ThreeSum.SourceBandLayout.len _root_.ThreeSum.SourceBandLayout.cap
  exact le_min (by omega) hg

theorem input_index {n g i j : ℕ} (hg : 0 < g) (hi : i < _root_.ThreeSum.BandPartition.size n g) (hj : j < _root_.ThreeSum.SourceBandLayout.len n g i) :
    _root_.ThreeSum.BandPartition.start g i+j < n := by
  have hlo := _root_.ThreeSum.BandPartition.start_lt_stop hg hi
  have hhi := _root_.ThreeSum.BandPartition.stop_le n g i
  unfold _root_.ThreeSum.SourceBandLayout.len at hj
  omega































end ThreeSum.SourceBandLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Evaluating a one-hot hash from a subset mask

The executable recursion examines exactly one bit per level using a cached
power of two.  Its result is the sum of the selected symbol coefficients,
and is connected here to the raw hashes used by the global encoding.
-/

namespace ThreeSum.OneHotMask
open _root_.ThreeSum.OneHotMask


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open scoped _root_.BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false











@[simp] theorem extend_fin {L : ℕ} (f : Fin L → ℕ) (i : Fin L) :
    _root_.ThreeSum.OneHotMask.extend f i.val = f i := by simp [_root_.ThreeSum.OneHotMask.extend, i.isLt]









end ThreeSum.OneHotMask

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-index incidences in the guarded global encoding

An incidence retains its original input indices, its complete sequence of
chosen-map occurrences and retained local edges, and its signed arithmetic
lift. Equal input values remain distinct original indices. The lift is
unique for a fixed original triple and representation, so it does not add
a factor of three to the representation bound.
-/

namespace ThreeSum.RawIncidences
open _root_.ThreeSum.RawIncidences


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds



theorem lift_small (j : Fin 3) : _root_.ThreeSum.Arithmetic.SmallLift (_root_.ThreeSum.RawIncidences.lift j) := by
  fin_cases j <;> simp [_root_.ThreeSum.RawIncidences.lift, _root_.ThreeSum.Arithmetic.SmallLift]

theorem lift_injective : Function.Injective _root_.ThreeSum.RawIncidences.lift := by
  intro i j hij
  apply Fin.ext
  unfold _root_.ThreeSum.RawIncidences.lift at hij
  omega











































theorem mem_witnesses {h J : ℕ} {P d a b c : ℤ} {w : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.Witness h J} :
    w ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses h J P d a b c ↔
      List.ofFn w.1 ∈ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representations h J (b % P) (c % P + d) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ (a % P + _root_.ThreeSum.RawIncidences.lift w.2 * P + d) - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleKey w.1 := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses, Finset.mem_filter, Finset.mem_univ, true_and]







/-- Projection to the retained list is injective on the raw witnesses of
one original triple: the guard makes its lift unique. -/
theorem witness_projection_injective {h J : ℕ} {P d a b c : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J) :
    Set.InjOn (fun w : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.Witness h J => List.ofFn w.1) (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses h J P d a b c) := by
  intro w hw v hv he
  have ht : w.1 = v.1 := List.ofFn_injective he
  have hwq := (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.mem_witnesses.mp hw).2
  have hvq := (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.mem_witnesses.mp hv).2
  have hd : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣
      (a % P + _root_.ThreeSum.RawIncidences.lift w.2 * P + d) - (a % P + _root_.ThreeSum.RawIncidences.lift v.2 * P + d) := by
    rw [ht] at hwq
    simpa only [sub_sub_sub_cancel_right] using dvd_sub hwq hvq
  have hj := _root_.ThreeSum1960614.Machine.ThreeSum.Arithmetic.guarded_lift_unique hP hguard (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.lift_small w.2) (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.lift_small v.2) hd
  exact Prod.ext ht (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.lift_injective hj)

theorem witnesses_card_bound {h J : ℕ} {P d a b c : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses h J P d a b c).card ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J := by
  calc
    _ ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representations h J (b % P) (c % P + d)).card := by
      apply Finset.card_le_card_of_injOn (fun w : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.Witness h J => List.ofFn w.1)
      · intro w hw
        exact (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.mem_witnesses.mp hw).1
      · exact _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witness_projection_injective hP hguard
    _ ≤ _ := _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representations_card_bound h J (b % P) (c % P + d)





section OriginalIndices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]























theorem rawMass_eq_sum_witnesses (h J : ℕ) (P d : ℤ) (T : Finset (_root_.ThreeSum.RawIncidences.Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawMass h J P d T a b c =
      ∑ t ∈ T, (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses h J P d (a t.1) (b t.2.1) (c t.2.2)).card :=
  Finset.card_sigma _ _























end OriginalIndices

end ThreeSum.RawIncidences

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Reading constructed block coefficients in the flat mask order

The imperative coefficient constructor writes rows. The mask evaluator reads
one flat array. These lemmas identify the two layouts, including empty ground
sets, and specialize them to the unchanged schedule-occurrence encoding.
-/

namespace ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.BlockCoefficientRows


open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds









@[simp] theorem occurrenceIndices_fin {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (i : Fin J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices o i.val = (o i).val := by
  exact _root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.extend_fin _ i















end ThreeSum.BlockCoefficientRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact row-major mask packing and prefix scan invariants -/

namespace ThreeSum.BlockMaskLayout
open _root_.ThreeSum.BlockMaskLayout


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators

























@[simp] theorem rawMasks_length {J L : ℕ} (rows : Fin J → Finset (Fin L)) :
    (_root_.ThreeSum.BlockMaskLayout.rawMasks rows).length = J := by simp [_root_.ThreeSum.BlockMaskLayout.rawMasks]





end ThreeSum.BlockMaskLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact sharing of source transforms and the encoder ledger

Source stages are indexed by a source band and an occurrence vector. The
output subset and the three-valued A lift do not enter the source function.
Compact table and zeta charges below match the existing `encoderCount`
without introducing a factor for all complete global outputs.
-/

namespace ThreeSum.BlockSourceSharing
open _root_.ThreeSum.BlockSourceSharing


open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds

theorem leftSource_eq_of_occurrences {β : Type*} [Fintype β] [DecidableEq β]
    {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ) {q q' : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J}
    (he : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q') :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource P B b q = _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource P B b q' := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource
  rw [he]

theorem rightSource_eq_of_occurrences {β : Type*} [Fintype β] [DecidableEq β]
    {h J : ℕ} (P d : ℤ) (B : Finset β) (b : β → ℤ) {q q' : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J}
    (he : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q') :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource P d B b q = _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource P d B b q' := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource
  rw [he]

theorem stored_left_reuse {β : Type*} [Fintype β] [DecidableEq β]
    {h J base cut : ℕ} {μ : ℕ → ℤ} (P : ℤ) (B : Finset β) (b : β → ℤ)
    {q q' : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J} (he : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q')
    (hs : _root_.ThreeSum.LightZetaStages.StoredThrough μ base cut (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource P B b q) (J*(464*h))) :
    _root_.ThreeSum.LightZetaStages.StoredThrough μ base cut (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource P B b q') (J*(464*h)) := by
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.leftSource_eq_of_occurrences P B b he]
  exact hs

theorem stored_right_reuse {β : Type*} [Fintype β] [DecidableEq β]
    {h J base cut : ℕ} {μ : ℕ → ℤ} (P d : ℤ) (B : Finset β) (b : β → ℤ)
    {q q' : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J} (he : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q')
    (hs : _root_.ThreeSum.LightZetaStages.StoredThrough μ base cut (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource P d B b q) (J*(464*h))) :
    _root_.ThreeSum.LightZetaStages.StoredThrough μ base cut (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource P d B b q') (J*(464*h)) := by
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.rightSource_eq_of_occurrences P d B b he]
  exact hs

























end ThreeSum.BlockSourceSharing

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
# Exact semantic interfaces for constructed local-cover tables

The concrete matrix constructor uses the unchanged radix enumeration of
the original local maps. Its retained histograms and gathered coefficient
rows are identified with the original occurrence-indexed encoding.
-/

namespace ThreeSum.LightLocalCoverTables
open _root_.ThreeSum.LightLocalCoverTables


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule











theorem Data.counts_read {μ : ℕ → ℤ} {h maps hist0 hist1 matrixPtr : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.Data μ h maps hist0 hist1 matrixPtr) {j r : ℕ} (hj : j < _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (hr : r < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) :
    μ (hist0+j*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+r) = (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.leftCount (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidate h j) h r : ℤ) ∧
    μ (hist1+j*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+r) = (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.rightCount (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidate h j) h r : ℤ) :=
  (H j hj).2.1 r hr







end ThreeSum.LightLocalCoverTables

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # A physical global-record index decodes to the original occurrence and mask rows -/

namespace ThreeSum.OutputDecodeRecords
open _root_.ThreeSum.OutputDecodeRecords


open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum.RadixKeyLists
open _root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000







theorem localCount_pos (h : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h := Nat.mul_pos (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.schedule_pos h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount_pos h)











theorem localIndex_lt {h J k j : ℕ} (hj : j < J) : _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localIndex h J k j < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h :=
  _root_.ThreeSum.OutputDecodeOrder.indices_getD_lt (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount_pos h) hj













theorem original_occurrence_index {h J k : ℕ} (hk : k < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J) (j : Fin J) :
    (((_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords h J).getD k (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.outputDefault h J)) j).1.val = _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.occurrenceIndex h J k j.val := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.global_record_block hk j,_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localRecords_getD (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localIndex_lt j.isLt)]
  rfl







end ThreeSum.OutputDecodeRecords

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact next-block masks for the reporting host

The machine enumerates subsets directly in the global row-major ground set.
This file identifies those subsets with the balanced next-row children of
the original reporting tree, and proves the arithmetic mask transitions.
-/

namespace ThreeSum.ReportingHostMasks
open _root_.ThreeSum.ReportingHostMasks


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockMaskLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced























theorem globalChildren_nodup {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (_root_.ThreeSum.ReportingHostMasks.globalChildren i Q h).Nodup := _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.missingSets_nodup _ _





theorem localChildren_nodup {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (_root_.ThreeSum.ReportingHostMasks.localChildren i Q h).Nodup := by
  apply (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.globalChildren_nodup i Q h).map_on
  intro S hS T hT he
  have hs := (_root_.ThreeSum.QueryCoordinates.missingSets_mem _ _ _).mp hS
  have ht := (_root_.ThreeSum.QueryCoordinates.missingSets_mem _ _ _).mp hT
  rw [← _root_.ThreeSum.ReportingHostMasks.blockSet_localRow i Q hs.1,← _root_.ThreeSum.ReportingHostMasks.blockSet_localRow i Q ht.1,he]



























end ThreeSum.ReportingHostMasks

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

/-!
# Constructed local-cover output as source-encoding input

This adapter connects the actual cover builder's retained candidate tables
and gathered occurrence rows to the exact reads used by source preparation.
Occurrence order, repeated candidates, and both independent bucket tables
are preserved without further searching or histogram construction.
-/

namespace ThreeSum.BlockSourceCoverInput
open _root_.ThreeSum.BlockSourceCoverInput


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.BlockSourceFlags
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags



theorem of_cover {μ : ℕ → ℤ} {h allMaps matrix maps candidates histL histR : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.Data μ h allMaps histL histR matrix)
    (R : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.ScheduleRows μ h maps)
    (I : ∀ s : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h,
      μ (candidates+s.val) = (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h s : ℤ)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCoverInput.Input μ h maps candidates histL histR := by
  refine ⟨I,?_,?_,?_,?_⟩
  · intro s hs t ht
    simpa only [Nat.mul_comm s (2*(464*h))] using (R s hs t ht).1
  · intro s hs t ht
    simpa only [Nat.mul_comm s (2*(464*h))] using (R s hs t ht).2
  · intro k hk r hr
    exact (H.counts_read hk hr).1
  · intro k hk r hr
    exact (H.counts_read hk hr).2



end ThreeSum.BlockSourceCoverInput

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



theorem code_indices {T M : ℕ} (hT : 0 < T) (hM : 0 < M) (J k : ℕ) :
    _root_.ThreeSum.OutputDecodeOrder.indices T J (_root_.ThreeSum.OutputDecodeOccurrenceCode.code T M J k) = (_root_.ThreeSum.OutputDecodeOrder.indices (T*M) J k).map (fun i => i/M) := by
  induction J generalizing k with
  | zero => rfl
  | succ J ih =>
    have hd := _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode.last_lt hT hM k
    have hdiv : _root_.ThreeSum.OutputDecodeOccurrenceCode.code T M (J+1) k/T = _root_.ThreeSum.OutputDecodeOccurrenceCode.code T M J (k/(T*M)) := by
      rw [_root_.ThreeSum.OutputDecodeOccurrenceCode.code,Nat.mul_comm T (_root_.ThreeSum.OutputDecodeOccurrenceCode.code T M J (k/(T*M))),
        Nat.add_mul_div_right _ _ hT,Nat.div_eq_of_lt hd,Nat.zero_add]
    have hmod : _root_.ThreeSum.OutputDecodeOccurrenceCode.code T M (J+1) k%T = (k%(T*M))/M := by
      have hm := Nat.div_add_mod (_root_.ThreeSum.OutputDecodeOccurrenceCode.code T M (J+1) k) T
      rw [hdiv] at hm
      have he : _root_.ThreeSum.OutputDecodeOccurrenceCode.code T M (J+1) k = (k%(T*M))/M+T*_root_.ThreeSum.OutputDecodeOccurrenceCode.code T M J (k/(T*M)) := rfl
      omega
    rw [_root_.ThreeSum.OutputDecodeOrder.indices,hdiv,hmod,ih]
    simp only [_root_.ThreeSum.OutputDecodeOrder.indices,List.map_append,List.map_cons,List.map_nil]

theorem source_code_lt (h J k : ℕ) :
    _root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J k < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h^J :=
  _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode.code_lt (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.schedule_pos h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount_pos h) J k

theorem source_code_coordinate (h J k : ℕ) {j : ℕ} (hj : j < J) :
    (_root_.ThreeSum.OutputDecodeOrder.indices (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) J (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J k)).getD j 0 =
      _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.occurrenceIndex h J k j := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode.code_indices (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.schedule_pos h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount_pos h)]
  have hi : j < (_root_.ThreeSum.OutputDecodeOrder.indices (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h*_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J k).length := by
    rw [_root_.ThreeSum.OutputDecodeOrder.indices_length]
    exact hj
  rw [_root_.List.getD_map_of_lt _ hi 0 0]
  rfl

end ThreeSum.OutputDecodeOccurrenceCode

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Coverage and raw-mass charging in the machine's actual child order

The output-sensitive enumerator uses its recursive coordinate order. The
reporting tree is instantiated with that exact order here; its positive
frontiers retain the original incidences and their multiplicities.
-/

namespace ThreeSum.ReportingHostFrontier
open _root_.ThreeSum.ReportingHostFrontier


open _root_.Finset
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open scoped _root_.BigOperators



theorem mem_children_iff {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ)
    (S : Finset (Fin (464*h))) : S ∈ _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.children q k ↔ S ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.children q k := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.children _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.children
  split
  · exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.localChildren_mem _ _ _ _
  · rfl

theorem children_nodup {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.children q k).Nodup := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.children
  split
  · exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks.localChildren_nodup _ _ _
  · exact List.nodup_nil



section Indices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]



theorem word_children {h J : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (r : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ) (hr : r ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain I w) (j : ℕ) (hj : j < J) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.word r)[j]'(by rw [_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.word,_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.partitionWord_length]; exact hj) ∈ _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.children w.2.2 j :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.mem_children_iff _ _ _).mpr (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.word_children I w r hr j hj)





theorem frontier_length_le_domain {h J k : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (hk : k ≤ J) : (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k).length ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain I w).card := by
  have h := _root_.ThreeSum.Reporting.frontier_length_le_mass (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain I w) _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.word (fun _ => 1)
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.children w.2.2) (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery I w) J k
    (fun r _ => _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.partitionWord_length r.2.1) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.word_children I w)
    (fun _ _ _ => rfl) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.children_nodup w.2.2) hk
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier,Finset.sum_const,smul_eq_mul,mul_one] using h

















end Indices

end ThreeSum.ReportingHostFrontier

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Bounded finite index types for the same physical owner products

The A type is the complete flattened incidence array; B and C are the
retained sorted arrays. Coordinate transport is injective and preserves
both each owner's product and its exact weighted collision score.
-/

namespace ThreeSum.BandRawA
open _root_.ThreeSum.BandRawA


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000













@[simp] theorem mem_finiteAIndices {n g s : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record}
    {i : Fin (_root_.ThreeSum.BandRawA.items n g rs).length} :
    i ∈ _root_.ThreeSum.BandRawA.finiteAIndices n g rs s ↔ i.val ∈ _root_.ThreeSum.BandRawA.aIndices n g rs s := by
  simp only [_root_.ThreeSum.BandRawA.finiteAIndices,mem_filter,mem_univ,true_and]







theorem finiteAIndices_owner {n g s : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record}
    (hs : s < rs.length) {i : Fin (_root_.ThreeSum.BandRawA.items n g rs).length} :
    i ∈ _root_.ThreeSum.BandRawA.finiteAIndices n g rs s ↔ (_root_.ThreeSum.BandRawA.labelAt n g rs i.val).owner=s := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.mem_finiteAIndices,_root_.ThreeSum.BandRawA.mem_aIndices_iff_owner hs]
  simp only [i.isLt,true_and]





















end ThreeSum.BandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact source-bank order and reuse by decoded global outputs

A source-bank row is the big-endian radix expansion of its physical index.
Its representative carries a fixed legal output subset solely to reuse the
original source definitions. No output-subset choice enters the stored row
or the source function. The actual global-output decoder supplies exactly
the bank index needed by a query.
-/

namespace ThreeSum.BlockSourceOccurrenceOrder
open _root_.ThreeSum.BlockSourceOccurrenceOrder


open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
open _root_.ThreeSum.OutputDecodeOccurrenceCode
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration







theorem row_coordinate {h J k j : ℕ} (hj : j < J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.representative h J k)) j =
      (_root_.ThreeSum.OutputDecodeOrder.indices (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) J k).getD j 0 := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices_fin _ ⟨j,hj⟩]
  rfl

theorem decoded_occurrences {h J k : ℕ} (hk : k < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.representative h J (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J k)) =
      _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences ((_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords h J).getD k (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.outputDefault h J)) := by
  funext j
  apply Fin.ext
  change (_root_.ThreeSum.OutputDecodeOrder.indices (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) J (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J k)).getD j.val 0 = _
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode.source_code_coordinate h J k j.isLt]
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.original_occurrence_index hk j).symm





end ThreeSum.BlockSourceOccurrenceOrder

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual shared source-stage catalog over occurrence vectors

One loop iteration constructs one retained bank and its two header pointers.
The original-band histograms and local-cover data are read throughout and
preserved. The semantic occurrence-row contract labels an ordinary physical
array; it does not assume any source-stage computation or output-subset loop.
-/

namespace ThreeSum.LightBlockSourceBatch
open _root_.ThreeSum.LightBlockSourceBatch


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000





theorem BankAt.reuse {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {h J base count cut i : ℕ} {μ : ℕ → ℤ} {P shift : ℤ}
    {B : Finset β} {b : β → ℤ} {A : Finset γ} {a : γ → ℤ} {q q' : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.BankAt μ base count cut i P shift B b A a q)
    (ho : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q') :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.BankAt μ base count cut i P shift B b A a q' :=
  ⟨_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.stored_left_reuse P B b ho H.left,
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.stored_right_reuse P shift A a ho H.right,H.headerLeft,H.headerRight⟩









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



end ThreeSum.LightBlockSourceBatch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact physical frontier slots and a capacity computed from root raw mass -/

namespace ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum.ReportingHostFrontierLayout


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false




















variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]



theorem rootMass_eq {h J : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w=(_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain I w).card := by
  simp [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass,_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery,_root_.ThreeSum.Reporting.mass,_root_.ThreeSum.Subset.fiberMass]






























end ThreeSum.ReportingHostFrontierLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact retained cells of one shared reporting catalog -/

namespace ThreeSum.SharedReportingBankData
open _root_.ThreeSum.SharedReportingBankData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData

set_option maxHeartbeats 1500000
set_option maxRecDepth 9000











theorem Tables.reporting {β γ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] {h J k : ℕ} {μ : ℕ → ℤ} {D : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog} {hk : k ≤ J}
    (p shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData.Tables μ D hk (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource p B b q)
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource p shift C c q)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Stored μ D hk p shift B C b c q :=
  ⟨H.index,H.pointers,H.boxes⟩

end ThreeSum.SharedReportingBankData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructed occurrence rows and their shared source banks

The first call constructs every big-endian occurrence row from its physical
bank index. The second call builds the two retained original source-stage
families once for that row. Original-band histograms and selected cover data
remain available throughout. No array of complete output records is read.
-/

namespace ThreeSum.LightBlockSourceCatalog
open _root_.ThreeSum.LightBlockSourceCatalog


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
open _root_.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000















theorem Stored.decoded {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {μ : ℕ → ℤ} {h J base cut k : ℕ} {P shift : ℤ}
    {B : Finset β} {b : β → ℤ} {A : Finset γ} {a : γ → ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.Stored μ h J base cut P shift B b A a) (hk : k < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.BankAt μ base (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) cut
      (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J k)
      P shift B b A a ((_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords h J).getD k (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.outputDefault h J)) :=
  (H _ (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode.source_code_lt h J k)).reuse (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.decoded_occurrences hk)

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



end ThreeSum.LightBlockSourceCatalog

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

theorem terminal_count_le (h J k : ℕ) : _root_.ThreeSum.LightReportingTerminalMasks.count h J k≤2^(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) := by
  have hh : (J-k)*(2*h)≤_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J := by
    exact (Nat.mul_le_mul_left _ (by omega : 2*h≤464*h)).trans
      (Nat.mul_le_mul_right _ (Nat.sub_le J k))
  exact (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide) hh)

theorem terminal_stop_mono {base W n T : ℕ} (hn : n≤T) :
    _root_.ThreeSum.LightReportingTerminalPreparation.stop base W n≤_root_.ThreeSum.LightReportingTerminalPreparation.stop base W T := by
  unfold _root_.ThreeSum.LightReportingTerminalPreparation.stop _root_.ThreeSum.LightReportingTerminalPreparation.span
  omega

section Mass

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem raw_card_le {h J : ℕ} {P shift : ℤ}
    (T : Finset (_root_.ThreeSum.RawIncidences.Original α β γ)) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (hP : 0<P) (hg : 4*P≤_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P shift T a b c).card≤T.card*_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J := by
  change _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawMass h J P shift T a b c≤_
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawMass_eq_sum_witnesses]
  calc
    _ ≤ ∑ _t∈T, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J := Finset.sum_le_sum (fun _ _ => _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses_card_bound hP hg)
    _ = _ := by simp

theorem root_mass_le {h J N NB NC : ℕ} {P shift : ℤ}
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (hP : 0<P) (hg : 4*P≤_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J)
    (hA : A.card≤N) (hB : B.card≤NB) (hC : C.card≤NC) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P shift (A ×ˢ (B ×ˢ C)) a b c) w≤
      _root_.ThreeSum.ReportingHostWantedLayout.massBound N NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass_eq]
  have hp : (A ×ˢ (B ×ˢ C)).card≤N*NB*NC := by
    rw [Finset.card_product,Finset.card_product]
    calc
      _ ≤ N*(NB*NC) := Nat.mul_le_mul hA (Nat.mul_le_mul hB hC)
      _ = _ := by ring
  exact (Finset.card_filter_le _ _).trans
    ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout.raw_card_le (A ×ˢ (B ×ˢ C)) a b c hP hg).trans
      (Nat.mul_le_mul_right _ hp))

theorem capacity_le {h J N NB NC : ℕ} {P shift : ℤ}
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (hP : 0<P) (hg : 4*P≤_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J)
    (hA : A.card≤N) (hB : B.card≤NB) (hC : C.card≤NC) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P shift (A ×ˢ (B ×ˢ C)) a b c) w≤
      _root_.ThreeSum.ReportingHostWantedLayout.capacityBound N NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J) (_root_.ThreeSum.LocalCoverBounds.groupSize h) :=
  Nat.mul_le_mul_right _ (Nat.add_le_add_right (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout.root_mass_le A B C a b c w hP hg hA hB hC) 1)

end Mass

end ThreeSum.ReportingHostWantedLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual emitted slots decide the complete physical owner domain

Each slot selects its own independently retained B/C bands. Its terminal
semantics is the exact finite owner fiber, while the cumulative guard uses
their disjoint global union. This connects the physical wanted array to
original-value terminal tests at every permitted partial reporting depth.
-/

namespace ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum.ReportingHostWantedOriginal


open _root_.Finset
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.ReportingHostWantedPhysical
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout

set_option maxHeartbeats 2300000
set_option maxRecDepth 12000



















theorem owner_lt {h J n g : ℕ} (rs : List _root_.ThreeSum.BandCandidateRows.Record) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (_root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.owner rs w<rs.length := (_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.at_bounds w.1.isLt).1

theorem mem_owner {h J n g : ℕ} (rs : List _root_.ThreeSum.BandCandidateRows.Record) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (_root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs)) :
    w.1∈_root_.ThreeSum.BandRawA.finiteAIndices n g rs (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.owner rs w) :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.finiteAIndices_owner (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.owner_lt rs w)).mpr rfl











section Actual

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n NB NC g free P h J : ℕ}
  {rs : List _root_.ThreeSum.BandCandidateRows.Record} {shift : ℤ}
  (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output μ free (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h^J)
    (_root_.ThreeSum.LightGuardedWanted.left P (_root_.ThreeSum.BandRawA.values fA (_root_.ThreeSum.BandRawA.items n g rs))) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right h J)
    (3*(_root_.ThreeSum.BandRawA.values fA (_root_.ThreeSum.BandRawA.items n g rs)).length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) shift)





end Actual

end ThreeSum.ReportingHostWantedOriginal

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact compact layout for a shared reporting catalog cell

The local pair and prefix counts are retained exactly. Each cell reserves
the two prefix arrays, its pointer row, all suffix boxes, the sorted index,
and the polynomial scratch used by the existing constructor. Layout sums
are later computed by the bank setup loop.
-/

namespace ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum.SharedReportingBankLayout


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog

set_option maxHeartbeats 1400000
set_option maxRecDepth 9000



























theorem ordered (base h J k boxCut : ℕ) :
    base ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL base h ∧ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL base h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR base h ∧ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR base h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL base h ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL base h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR base h k ∧ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR base h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers base h k ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers base h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes base h k ∧ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes base h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks base h J k boxCut ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks base h J k boxCut ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work base h J k boxCut ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work base h J k boxCut ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish base h J k boxCut := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL]
  omega

theorem finish_add (base h J k boxCut : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish base h J k boxCut=base+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cellSize h J k boxCut := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cellSize _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL
  omega



theorem index_end (base h J k boxCut : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.index base h J k boxCut+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work base h J k boxCut := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.index _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work
  omega















theorem levelOffset_step (h J : ℕ) (boxCut : ℕ → ℕ) (k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset h J boxCut k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset h J boxCut (k+1) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset]
  omega

theorem levelOffset_mono (h J : ℕ) (boxCut : ℕ → ℕ) : Monotone (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset h J boxCut) :=
  monotone_nat_of_le_succ (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset_step h J boxCut)

theorem finish_level (base h J k : ℕ) (boxCut : ℕ → ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish (base+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset h J boxCut k) h J k (boxCut k)=
      base+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset h J boxCut (k+1) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish_add,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset]
  omega

end ThreeSum.SharedReportingBankLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact level layout and retention for one shared source pair -/

namespace ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum.SharedReportingBankLevels


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData

set_option maxHeartbeats 1400000
































theorem baseAt_mono (base h J : ℕ) : Monotone (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J) := by
  intro i j hij
  exact Nat.add_le_add_left (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.levelOffset_mono h J (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J) hij) base

theorem finish_baseAt (base h J k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h J k (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k)=_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J (k+1) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish_level base h J k (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J)



theorem catalog_end (base h J k : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt base h J k).indexBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J (k+1) ∧
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt base h J k).ptrBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J (k+1) ∧
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt base h J k).boxBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k*
      _root_.ThreeSum.LightReportingSuffixCatalog.stride ((J-k)*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J (k+1) := by
  have ho := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.ordered (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h J k (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k)
  have hi := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.index_end (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h J k (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k)
  have hp : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h k+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k=_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h k := rfl
  have hm : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h k+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k*
      _root_.ThreeSum.LightReportingSuffixCatalog.stride ((J-k)*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k)=_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt base h J k) h J k (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k) := rfl
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.finish_baseAt]
  dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalogAt,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.catalog]
  omega





end ThreeSum.SharedReportingBankLevels

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Complete source banks per common band with preserved earlier banks -/

namespace ThreeSum.SourceBandBankLayout
open _root_.ThreeSum.SourceBandBankLayout


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder























theorem At.decoded {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g h J cut i k : ℕ}
    {p shift : ℤ} (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.At μ fL fR base NL NR g h J cut p shift i)
    (hk : k < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.BankAt μ (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.baseAt base h J cut i) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) cut
      (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J k)
      p shift (_root_.ThreeSum.SourceBandPartition.source NL g i) (fun t : Fin NL => fL t.val)
      (_root_.ThreeSum.SourceBandPartition.source NR g i) (fun t : Fin NR => fR t.val)
      ((_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords h J).getD k (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.outputDefault h J)) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.Stored.decoded H hk

end ThreeSum.SourceBandBankLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retained common-band source catalog with one occurrence table -/

namespace ThreeSum.SourceBandBankData
open _root_.ThreeSum.SourceBandBankData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords








theorem Stored.decoded {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g h J cut occ i k : ℕ} {p shift : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.Stored μ fL fR base NL NR g h J cut occ p shift)
    (hi : i < _root_.ThreeSum.SourceBandPairSlices.count NL NR g) (hk : k < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.BankAt μ (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.baseAt (_root_.ThreeSum.SourceBandBankData.first base) h J cut i) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) cut
      (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J k)
      p shift (_root_.ThreeSum.SourceBandPartition.source NL g i) (fun t : Fin NL => fL t.val)
      (_root_.ThreeSum.SourceBandPartition.source NR g i) (fun t : Fin NR => fR t.val)
      ((_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords h J).getD k (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.outputDefault h J)) :=
  (H.banks i hi).decoded hk





end ThreeSum.SourceBandBankData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Independent source bands and exact reuse for every decoded output -/

namespace ThreeSum.SharedReportingBankSources
open _root_.ThreeSum.SharedReportingBankSources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords














theorem tables_reuse {β γ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] {h J k : ℕ} {μ : ℕ → ℤ}
    {D : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog} {hk : k ≤ J}
    (p shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    {q q' : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J} (ho : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q=_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q')
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData.Tables μ D hk (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource p B b q) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource p shift C c q)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData.Tables μ D hk (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource p B b q') (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource p shift C c q') := by
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.leftSource_eq_of_occurrences p B b ho,
    ← _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.rightSource_eq_of_occurrences p shift C c ho]
  exact H



theorem reporting_decoded {β γ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] {h J k output record : ℕ} {μ : ℕ → ℤ}
    {D : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog} {hk : k ≤ J}
    (p shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (houtput : output < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J)
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData.Entry μ record D hk
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource p B b (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.representative h J
        (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J output)))
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource p shift C c (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.representative h J
        (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J output)))) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Stored μ D hk p shift B C b c
      ((_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords h J).getD output (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.outputDefault h J)) :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.tables_reuse p shift B C b c (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.decoded_occurrences houtput) H.tables).reporting p shift B C b c _

end ThreeSum.SharedReportingBankSources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # The shared source banks in the physical finite reporting domains -/

namespace ThreeSum.SourceBandFinite
open _root_.ThreeSum.SourceBandFinite


open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords

theorem source_eq_finiteBandPositions (n g i : ℕ) :
    _root_.ThreeSum.SourceBandPartition.source n g i=_root_.ThreeSum.BandRawA.finiteBandPositions n g i := by
  ext t
  rw [_root_.ThreeSum.SourceBandPartition.mem_source,_root_.ThreeSum.BandRawA.mem_finiteBandPositions,_root_.ThreeSum.BandRawA.mem_bandPositions]





theorem decoded {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g h J cut occ i k : ℕ} {p shift : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.Stored μ fL fR base NL NR g h J cut occ p shift)
    (hi : i < _root_.ThreeSum.SourceBandPairSlices.count NL NR g) (hk : k < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.BankAt μ (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.baseAt (base+5) h J cut i)
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) cut
      (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J k) p shift
      (_root_.ThreeSum.BandRawA.finiteBandPositions NL g i) (fun t : Fin NL => fL t.val)
      (_root_.ThreeSum.BandRawA.finiteBandPositions NR g i) (fun t : Fin NR => fR t.val)
      ((_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords h J).getD k (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.outputDefault h J)) := by
  simpa only [_root_.ThreeSum.SourceBandBankData.first,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandFinite.source_eq_finiteBandPositions] using H.decoded hi hk

end ThreeSum.SourceBandFinite

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Selected controls from the actual retained original-source catalogs

The selector's concrete header reads follow from the existing band,
occurrence-bank and local-cover constructors. Its two independently chosen
bands supply the unchanged physical buckets and the exact original-output
source stages. No output-subset loop or source reconstruction is involved.
-/

namespace ThreeSum.ReportingHostSourceSelectionStored
open _root_.ThreeSum.ReportingHostSourceSelectionStored


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.ReportingHostSourceSelection
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelection
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows

set_option maxHeartbeats 2300000
set_option maxRecDepth 12000







theorem sources_decoded {μ : ℕ→ℤ} {fB fC : ℕ→ℤ}
    {pair bank cover NL NR g p h J occ i j output : ℕ} {shift : ℤ}
    (HB : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.Stored μ fB fC bank NL NR g h J (_root_.ThreeSum.LightBlockQuery.sourceCut h J) occ (p : ℤ) shift)
    (hi : i<_root_.ThreeSum.BandPartition.size NL g) (hj : j<_root_.ThreeSum.BandPartition.size NR g)
    (hk : output<_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J) :
    let code := _root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J output
    let X := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored.retained pair bank cover NL NR g h J (_root_.ThreeSum.LightBlockQuery.sourceCut h J) occ i j code
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Sources μ (p : ℤ) shift
      (_root_.ThreeSum.BandRawA.finiteBandPositions NL g i) (_root_.ThreeSum.BandRawA.finiteBandPositions NR g j)
      (fun t : Fin NL => fB t.val) (fun t : Fin NR => fC t.val)
      ((_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords h J).getD output (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.outputDefault h J)) X.stagesL X.stagesR := by
  have hLi : i<_root_.ThreeSum.SourceBandPairSlices.count NL NR g := hi.trans_le (le_max_left _ _)
  have hRj : j<_root_.ThreeSum.SourceBandPairSlices.count NL NR g := hj.trans_le (le_max_right _ _)
  exact ⟨(_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandFinite.decoded HB hLi hk).left,(_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandFinite.decoded HB hRj hk).right⟩

theorem occurrence_rows_decoded {μ : ℕ→ℤ} {fB fC : ℕ→ℤ}
    {pair bank cover NL NR g p h J cut occ i j output : ℕ} {shift : ℤ}
    (HB : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.Stored μ fB fC bank NL NR g h J cut occ (p : ℤ) shift)
    (hk : output<_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J) (t : ℕ) (ht : t<J) :
    let code := _root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J output
    let X := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored.retained pair bank cover NL NR g h J cut occ i j code
    μ (_root_.ThreeSum.ReportingHostSourceSelection.occurrenceRow X code J+t)=
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences
        ((_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords h J).getD output (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.outputDefault h J))) t : ℤ) := by
  have H := HB.rows _ (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode.source_code_lt h J output) t ht
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.row_coordinate ht,
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.decoded_occurrences hk] at H
  exact H







end ThreeSum.ReportingHostSourceSelectionStored

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












theorem rowBase_next (base h J K q : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rowBase base h J K q) h J K=_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rowBase base h J K (q+1) := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rowBase _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt
  ring
theorem rowBase_mono (base h J K : ℕ) : Monotone (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rowBase base h J K) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _











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








theorem records_le_payload (free h J NB NC g : ℕ) :
    _root_.ThreeSum.SharedReportingBankHeader.records free ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload free h J NB NC g := Nat.le_add_right _ _
theorem payload_le_finish (free h J NB NC g : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload free h J NB NC g ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish free h J NB NC g := Nat.le_add_right _ _












theorem Stored.row {μ : ℕ → ℤ} {free h J NB NC g s i j : ℕ}
    {fB fC : ℕ → ℤ} {p shift : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.Stored μ free h J NB NC g fB fC p shift)
    (hs : s < _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (hi : i < _root_.ThreeSum.BandPartition.size NB g)
    (hj : j < _root_.ThreeSum.BandPartition.size NC g) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.Built μ (_root_.ThreeSum.SharedReportingBankRows.rowRecord (_root_.ThreeSum.SharedReportingBankHeader.records free) (_root_.ThreeSum.SharedReportingBankHeader.levels J) (_root_.ThreeSum.SharedReportingBankRows.rank (_root_.ThreeSum.BandPartition.size NB g) (_root_.ThreeSum.BandPartition.size NC g) s i j))
      (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rowBase (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload free h J NB NC g) h J (_root_.ThreeSum.SharedReportingBankHeader.levels J) (_root_.ThreeSum.SharedReportingBankRows.rank (_root_.ThreeSum.BandPartition.size NB g) (_root_.ThreeSum.BandPartition.size NC g) s i j))
      h J (_root_.ThreeSum.SharedReportingBankHeader.levels J)
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource p (_root_.ThreeSum.SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val)
        (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.representative h J s))
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource p shift (_root_.ThreeSum.SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val)
        (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.representative h J s)) :=
  H.rows s hs i hi j hj (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rank_lt hs hi hj)

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

theorem row_end {free h J NB NC g s i j : ℕ}
    (hs : s < _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (hi : i < _root_.ThreeSum.BandPartition.size NB g)
    (hj : j < _root_.ThreeSum.BandPartition.size NC g) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.payloadAt free h J NB NC g s i j) h J (_root_.ThreeSum.SharedReportingBankHeader.levels J) ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish free h J NB NC g := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.payloadAt
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rowBase_next]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rowBase_mono _ h J (_root_.ThreeSum.SharedReportingBankHeader.levels J) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rank_lt hs hi hj)

theorem level_end {free h J NB NC g s i j k : ℕ}
    (hs : s < _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (hi : i < _root_.ThreeSum.BandPartition.size NB g)
    (hj : j < _root_.ThreeSum.BandPartition.size NC g) (hk : k < _root_.ThreeSum.SharedReportingBankHeader.levels J) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.levelCatalog free h J NB NC g s i j k).indexBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish free h J NB NC g ∧
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.levelCatalog free h J NB NC g s i j k).ptrBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish free h J NB NC g ∧
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.levelCatalog free h J NB NC g s i j k).boxBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k*
      _root_.ThreeSum.LightReportingSuffixCatalog.stride ((J-k)*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.levelCatalog free h J NB NC g s i j k).boxCut ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish free h J NB NC g := by
  have hend := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.catalog_end (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.payloadAt free h J NB NC g s i j) h J k
  have hbefore := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.baseAt_mono (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.payloadAt free h J NB NC g s i j) h J
    (show k+1 ≤ _root_.ThreeSum.SharedReportingBankHeader.levels J from hk)).trans (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.row_end hs hi hj)
  exact ⟨hend.1.trans hbefore,hend.2.1.trans hbefore,hend.2.2.trans hbefore⟩

theorem entry {μ : ℕ → ℤ} {free h J NB NC g s i j k : ℕ} {fB fC : ℕ → ℤ} {p shift : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.Stored μ free h J NB NC g fB fC p shift)
    (hs : s < _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (hi : i < _root_.ThreeSum.BandPartition.size NB g)
    (hj : j < _root_.ThreeSum.BandPartition.size NC g) (hk : k < _root_.ThreeSum.SharedReportingBankHeader.levels J) (hkJ : k ≤ J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData.Entry μ (_root_.ThreeSum.SharedReportingBankAccess.recordAt free J NB NC g s i j+5*k) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.levelCatalog free h J NB NC g s i j k) hkJ
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource p (_root_.ThreeSum.SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val)
        (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.representative h J s))
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource p shift (_root_.ThreeSum.SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val)
        (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder.representative h J s)) := by
  obtain ⟨hk',Hk⟩ := H.row hs hi hj k hk
  exact Hk

theorem bounds {source free h J NB NC g s i j k stop : ℕ}
    (hs : s < _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (hi : i < _root_.ThreeSum.BandPartition.size NB g)
    (hj : j < _root_.ThreeSum.BandPartition.size NC g) (hk : k < _root_.ThreeSum.SharedReportingBankHeader.levels J)
    (hsource : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish source NB NC g h J (2*h*J) ≤ free)
    (hstop : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish free h J NB NC g ≤ stop) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Bounds h J k (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.levelCatalog free h J NB NC g s i j k)
      (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.leftBase source h J (2*h*J) i s) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.rightBase source h J (2*h*J) j s) stop := by
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.source_bounds (base := source) (NB := NB) (NC := NC) (cut := 2*h*J)
    (hi.trans_le (le_max_left _ _)) hs
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.source_bounds (base := source) (NB := NB) (NC := NC) (cut := 2*h*J)
    (hj.trans_le (le_max_right _ _)) hs
  have hf : free ≤ stop := (Nat.le_add_right free 9).trans
    ((_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.records_le_payload free h J NB NC g).trans ((_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload_le_finish free h J NB NC g).trans hstop))
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.level_end (free := free) hs hi hj hk
  exact ⟨hl.2.2.1.trans (hsource.trans hf),hr.2.2.2.trans (hsource.trans hf),
    he.1.trans hstop,he.2.1.trans hstop,he.2.2.trans hstop⟩

theorem original {μ : ℕ → ℤ} {free h J NB NC g output i j k : ℕ}
    {fB fC : ℕ → ℤ} {p shift : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.Stored μ free h J NB NC g fB fC p shift)
    (houtput : output < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J) (hi : i < _root_.ThreeSum.BandPartition.size NB g)
    (hj : j < _root_.ThreeSum.BandPartition.size NC g) (hk : k < _root_.ThreeSum.SharedReportingBankHeader.levels J) (hkJ : k ≤ J) :
    let s := _root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J output
    _root_.ThreeSum1960614.Machine.Light.SegN μ (_root_.ThreeSum.SharedReportingBankAccess.recordAt free J NB NC g s i j+5*k) ((_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.levelCatalog free h J NB NC g s i j k).record h k) ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Stored μ (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.levelCatalog free h J NB NC g s i j k) hkJ p shift
      (_root_.ThreeSum.BandRawA.finiteBandPositions NB g i) (_root_.ThreeSum.BandRawA.finiteBandPositions NC g j)
      (fun t : Fin NB => fB t.val) (fun t : Fin NC => fC t.val)
      ((_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords h J).getD output (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.outputDefault h J)) := by
  have hs : _root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J output <
      _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J := _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode.source_code_lt h J output
  have Hk := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.entry H hs hi hj hk hkJ
  refine ⟨Hk.header,?_⟩
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandFinite.source_eq_finiteBandPositions] using
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.reporting_decoded p shift (_root_.ThreeSum.SourceBandPartition.source NB g i) (_root_.ThreeSum.SourceBandPartition.source NC g j)
      (fun t : Fin NB => fB t.val) (fun t : Fin NC => fC t.val) houtput Hk

end ThreeSum.SharedReportingBankAccess

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

















theorem rawRows_end (layoutHeader J : ℕ) : _root_.ThreeSum.ReportingHostWantedControls.rawRows layoutHeader J+J=_root_.ThreeSum.ReportingHostWantedLayout.access layoutHeader J := by
  rfl

theorem rawRows_before_packed (layoutHeader J : ℕ) : _root_.ThreeSum.ReportingHostWantedControls.rawRows layoutHeader J+J≤_root_.ThreeSum.ReportingHostWantedLayout.packed layoutHeader J := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls.rawRows_end]
  exact Nat.le_add_right _ _



end ThreeSum.ReportingHostWantedControls

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



























section Raw

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem wanted_frontier_length_le {h J K N NB NC : ℕ} {P shift : ℤ}
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (hK : K≤J) (hP : 0<P) (hg : 4*P≤_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J)
    (hA : A.card≤N) (hB : B.card≤NB) (hC : C.card≤NC) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P shift (A ×ˢ (B ×ˢ C)) a b c) w K).length≤
      _root_.ThreeSum.ReportingHostWantedLayout.massBound N NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J) := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier_length_le_domain
    (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P shift (A ×ˢ (B ×ˢ C)) a b c) w hK
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass_eq] at hh
  exact hh.trans (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout.root_mass_le A B C a b c w hP hg hA hB hC)

theorem wanted_depth {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {h J K N NB NC d : ℕ} {P shift : ℤ}
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (hK : K≤J) (hP : 0<P) (hg : 4*P≤_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J)
    (hA : A.card≤N) (hB : B.card≤NB) (hC : C.card≤NC)
    (hd : d+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedDepth h J K N NB NC≤lim.depth) :
    d+K+2*_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P shift (A ×ˢ (B ×ˢ C)) a b c) w K).length+
      _root_.ThreeSum.LightReportingTerminalMasks.count h J K+30≤lim.depth := by
  have hf := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_frontier_length_le (shift := shift) A B C a b c w hK hP hg hA hB hC
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout.terminal_count_le h J K
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedDepth at hd
  omega



end Raw
end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-domain facts carried by the two actual wanted records

All source stages, buckets, occurrence rows, and per-level catalogs below
come from the retained concrete constructors. The decoder supplies the
unaltered original Q masks used by the guarded reporter.
-/

namespace ThreeSum.ReportingHostWantedRecordData
open _root_.ThreeSum.ReportingHostWantedRecordData


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
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords

set_option maxHeartbeats 2300000
set_option maxRecDepth 14000
set_option linter.unusedSectionVars false





theorem selected_value (fA : ℕ→ℤ) (n NB NC g pair bank cover h J occ srcB srcC report : ℕ)
    (rs : List _root_.ThreeSum.BandCandidateRows.Record) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (_root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs)) (output : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output).av=
      _root_.ThreeSum.BandRawA.valueAt n g rs fA w.1.val := by
  change fA (_root_.ThreeSum.BandRawA.labelAt n g rs w.1.val).position=(_root_.ThreeSum.BandRawA.values fA (_root_.ThreeSum.BandRawA.items n g rs)).getD w.1.val 0
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.values_getD fA w.1.isLt).symm





section Stored

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ}
  {n NB NC g pair bank cover h J p occ srcB srcC report output : ℕ}
  {rs : List _root_.ThreeSum.BandCandidateRows.Record} {shift : ℤ} (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (_root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs))

theorem sources
    (HB : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.Stored μ fB fC bank NB NC g h J
      (_root_.ThreeSum.LightBlockQuery.sourceCut h J) occ (p : ℤ) shift)
    (hi : (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).b<_root_.ThreeSum.BandPartition.size NB g)
    (hj : (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).c<_root_.ThreeSum.BandPartition.size NC g)
    (houtput : output<_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J) (he : w.2.2=_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeOriginal.output h J output) :
    let S := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Sources μ (p : ℤ) shift
      (_root_.ThreeSum.BandRawA.finiteBandPositions NB g (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).b)
      (_root_.ThreeSum.BandRawA.finiteBandPositions NC g (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).c)
      (fun i : Fin NB => fB i.val) (fun i : Fin NC => fC i.val) w.2.2 S.baseL S.baseR := by
  rw [he]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored.sources_decoded (pair := pair) (cover := cover) HB hi hj houtput

theorem catalog
    (HQ : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.Stored μ report h J NB NC g fB fC (p : ℤ) shift)
    (hi : (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).b<_root_.ThreeSum.BandPartition.size NB g)
    (hj : (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).c<_root_.ThreeSum.BandPartition.size NC g)
    (houtput : output<_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J) (he : w.2.2=_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeOriginal.output h J output)
    {k : ℕ} (hk : k<_root_.ThreeSum.SharedReportingBankHeader.levels J) (hkJ : k≤J) :
    let S := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
    let D := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.catalogs n NB NC g report h J rs w output k
    _root_.ThreeSum1960614.Machine.Light.SegN μ (S.catalog+5*k) (D.record h k) ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Stored μ D hkJ (p : ℤ) shift
        (_root_.ThreeSum.BandRawA.finiteBandPositions NB g (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).b)
        (_root_.ThreeSum.BandRawA.finiteBandPositions NC g (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).c)
        (fun i : Fin NB => fB i.val) (fun i : Fin NC => fC i.val) w.2.2 := by
  rw [he]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.original HQ houtput hi hj hk hkJ

theorem buckets
    (HP : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.Stored μ fB fC pair NB NC g p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift)
    (hi : (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).b<_root_.ThreeSum.BandPartition.size NB g)
    (hj : (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).c<_root_.ThreeSum.BandPartition.size NC g) :
    let S := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ (fun i => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 0 (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.left rs fB w i))
      S.NL (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) S.offsetsL S.flatL ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ (fun i => _root_.ThreeSum.LightSourceResidues.key p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.right rs fC w i))
      S.NR (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) S.offsetsR S.flatR :=
  ⟨(HP.left _ hi).buckets,(HP.right _ hj).buckets⟩

theorem occurrences
    (HB : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.Stored μ fB fC bank NB NC g h J
      (_root_.ThreeSum.LightBlockQuery.sourceCut h J) occ (p : ℤ) shift)
    (houtput : output<_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J) (he : w.2.2=_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeOriginal.output h J output)
    {t : ℕ} (ht : t<J) :
    let S := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
    μ (S.occ+t)=(_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences w.2.2) t : ℤ) := by
  rw [he]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored.occurrence_rows_decoded HB houtput t ht

theorem cover_input (HC : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.Stored μ cover h J) :
    let S := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCoverInput.Input μ h S.maps S.candidates S.histL S.histR :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCoverInput.of_cover HC.data HC.rows HC.indices

theorem source_reads (hg : 0<g)
    (hi : (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).b<_root_.ThreeSum.BandPartition.size NB g)
    (hj : (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).c<_root_.ThreeSum.BandPartition.size NC g)
    (hreadB : ∀ i<NB, μ (srcB+i)=fB i) (hreadC : ∀ i<NC, μ (srcC+i)=fC i) :
    let S := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
    (∀ i<S.NL, μ (S.srcL+i)=_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.left rs fB w i) ∧
      (∀ i<S.NR, μ (S.srcR+i)=_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.right rs fC w i) := by
  constructor
  · intro i hi'
    have hh := hreadB _ (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.input_index hg hi hi')
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.selected,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls.ofAccess,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess.selection,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored.retained,
      _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.left,Nat.add_assoc] using hh
  · intro i hi'
    have hh := hreadC _ (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.input_index hg hj hi')
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.selected,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls.ofAccess,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess.selection,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored.retained,
      _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.right,Nat.add_assoc] using hh

theorem raw_rows {dst N i : ℕ}
    (HD : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.Stored μ (_root_.ThreeSum.ReportingHostWantedLayout.decoded dst) N h J i output)
    (he : w.2.2=_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeOriginal.output h J output) :
    _root_.ThreeSum1960614.Machine.Light.SegN μ (_root_.ThreeSum.ReportingHostWantedControls.rawRows dst J) (_root_.ThreeSum.BlockMaskLayout.rawMasks (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2)) := by
  intro t ht
  have ht' : t<J := by simpa only [List.length_map,_root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout.rawMasks_length] using ht
  have hh := HD.rows.masks ⟨t,ht'⟩
  simpa only [he,_root_.ThreeSum.ReportingHostWantedControls.rawRows,_root_.ThreeSum.BlockMaskLayout.rawMasks,_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows,List.getElem_map,List.getElem_ofFn] using hh

end Stored



end ThreeSum.ReportingHostWantedRecordData

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











theorem wanted_catalog_bounds {pair bank cover report NB NC g h J occ i j code stop K : ℕ}
    (hi : i<_root_.ThreeSum.BandPartition.size NB g) (hj : j<_root_.ThreeSum.BandPartition.size NC g)
    (hk : code<_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (hK : K≤_root_.ThreeSum.LightSwitchDepth.depth J)
    (hbank : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish bank NB NC g h J (_root_.ThreeSum.LightBlockQuery.sourceCut h J)≤report)
    (hreport : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish report h J NB NC g≤ stop) :
    _root_.ThreeSum.SharedReportingBankAccess.recordAt report J NB NC g code i j+5*(K+1)≤ stop ∧
    ∀ k≤K, _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Bounds h J k
      (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.levelCatalog report h J NB NC g code i j k)
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored.retained pair bank cover NB NC g h J (_root_.ThreeSum.LightBlockQuery.sourceCut h J) occ i j code).stagesL
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSourceSelectionStored.retained pair bank cover NB NC g h J (_root_.ThreeSum.LightBlockQuery.sourceCut h J) occ i j code).stagesR stop := by
  have he := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.record_end (free := report) hk hi hj).trans
    ((_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload_le_finish report h J NB NC g).trans hreport)
  refine ⟨?_,?_⟩
  · unfold _root_.ThreeSum.SharedReportingBankHeader.levels at he
    omega
  · intro k hkk
    exact _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.bounds hk hi hj (by unfold _root_.ThreeSum.SharedReportingBankHeader.levels; omega) hbank hreport

end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecord

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
set_option maxHeartbeats 3500000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecord.program_meets__implementation_2500f96b4b {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ}
    {n NB NC g pair bank cover h J p occ srcB srcC report output dst counter K old threshold V d i : ℕ}
    {rs : List _root_.ThreeSum.BandCandidateRows.Record} {shift : ℤ}
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (_root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs))
    (HP : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.Stored μ fB fC pair NB NC g p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift)
    (HB : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.Stored μ fB fC bank NB NC g h J
      (_root_.ThreeSum.LightBlockQuery.sourceCut h J) occ (p : ℤ) shift)
    (HC : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.Stored μ cover h J)
    (HQ : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.Stored μ report h J NB NC g fB fC (p : ℤ) shift)
    (hi : (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).b<_root_.ThreeSum.BandPartition.size NB g)
    (hj : (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).c<_root_.ThreeSum.BandPartition.size NC g)
    (houtput : output<_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J) (he : w.2.2=_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeOriginal.output h J output)
    (hg : 0<g) (hp : 0<p) (hguard : 4*(p : ℤ)≤_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J)
    (hK : K≤_root_.ThreeSum.LightSwitchDepth.depth J) (hKJ : K≤J)
    (hkey : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J∣ _root_.ThreeSum.BandRawA.valueAt n g rs fA w.1.val%(p : ℤ)+
      _root_.ThreeSum.RawIncidences.lift w.2.1*(p : ℤ)+shift-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2)
    (hselected : _root_.ThreeSum1960614.Machine.Light.Seg μ (_root_.ThreeSum.ReportingHostWantedLayout.access dst J)
      (_root_.ThreeSum.ReportingHostWantedControls.record (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output)))
    (hlayout : _root_.ThreeSum1960614.Machine.Light.SegN μ dst (_root_.ThreeSum.ReportingHostWantedLayout.values (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout dst h J K (_root_.ThreeSum.BandRawA.items n g rs).length NB NC)))
    (hdecoded : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.Stored μ (_root_.ThreeSum.ReportingHostWantedLayout.decoded dst) (_root_.ThreeSum.BandRawA.items n g rs).length h J i output)
    (hcounter : counter+4≤dst)
    (hcounterRead : μ counter=(old : ℤ)) (hthreshold : μ (counter+1)=(threshold : ℤ))
    (hends : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.WantedSourceEnds
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedAccess.selection n g rs w.1.val pair bank cover NB NC h J
        (_root_.ThreeSum.LightBlockQuery.sourceCut h J) occ (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J output))
      pair bank cover srcB srcC (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).b (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).c
      (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J output) h J
      (_root_.ThreeSum.LightBlockQuery.sourceCut h J) counter)
    (hbank : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish bank NB NC g h J (_root_.ThreeSum.LightBlockQuery.sourceCut h J)≤report)
    (hreport : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish report h J NB NC g≤counter)
    (hbuffers : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.WantedBuffers lim dst h J K (_root_.ThreeSum.BandRawA.items n g rs).length NB NC V)
    (hqueries : ∀ k≤K, _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Scratch lim h J k
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.catalogs n NB NC g report h J rs w output k)
      (_root_.ThreeSum.BandRawA.finiteBandPositions NB g (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).b).card
      (_root_.ThreeSum.BandRawA.finiteBandPositions NC g (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).c).card
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout dst h J K (_root_.ThreeSum.BandRawA.items n g rs).length NB NC).maskBase
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout dst h J K (_root_.ThreeSum.BandRawA.items n g rs).length NB NC).work)
    (hw : (lim.space : ℤ)≤lim.word)
    (hrecordSpace : _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall.space (_root_.ThreeSum.ReportingHostWantedLayout.access dst J) dst cover counter h J K≤lim.space)
    (hselectedWords : ∀ z∈_root_.ThreeSum.ReportingHostWantedControls.record (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output), |z|≤lim.word)
    (hguardWord : ((old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.localItems h J n NB NC g p rs fA fB fC shift w) w+threshold+2 : ℕ) : ℤ)≤lim.word)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminal.word h J : ℤ)≤lim.word)
    (hreadB : ∀ j<NB, μ (srcB+j)=fB j) (hreadC : ∀ j<NC, μ (srcC+j)=fC j)
    (hvaluesB : ∀ j<NB, |fB j|≤lim.word) (hvaluesC : ∀ j<NC, |fC j|≤lim.word)
    (htarget : ∀ j<NB, |_root_.ThreeSum.BandRawA.valueAt n g rs fA w.1.val+fB j|≤lim.word)
    (hcountWord : ((NB*NC : ℕ) : ℤ)≤lim.word)
    (hd : d+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedDepth h J K (_root_.ThreeSum.BandRawA.items n g rs).length NB NC≤lim.depth) :
    let S := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
    let D := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.catalogs n NB NC g report h J rs w output
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall.program 138 d
      [_root_.ThreeSum.ReportingHostWantedLayout.access dst J,dst,h,J,K,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,cover,counter] μ
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWanted.time p shift (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.left rs fB w) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.right rs fC w)
        S.NL S.NR old threshold (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.localItems h J n NB NC g p rs fA fB fC shift w) w D K+4000)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ threshold<old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.localItems h J n NB NC g p rs fA fB fC shift w) w ∨
          _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.Terminal h J n NB NC g p rs fA fB fC shift w K) ∧
        ν counter=((old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.localItems h J n NB NC g p rs fA fB fC shift w) w : ℕ) : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν (_root_.ThreeSum.ReportingHostWantedLayout.packed dst J) counter 1) := by
  let S := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
  let D := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.catalogs n NB NC g report h J rs w output
  let L := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedLayout.layout dst h J K (_root_.ThreeSum.BandRawA.items n g rs).length NB NC
  let A := _root_.ThreeSum.BandRawA.finiteAIndices n g rs (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.owner rs w)
  let B := _root_.ThreeSum.BandRawA.finiteBandPositions NB g (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).b
  let C := _root_.ThreeSum.BandRawA.finiteBandPositions NC g (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).c
  let a := fun i : _root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs => _root_.ThreeSum.BandRawA.valueAt n g rs fA i.val
  let b := fun i : Fin NB => fB i.val
  let c := fun i : Fin NC => fC i.val
  let I := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
  have hI : I=_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.localItems h J n NB NC g p rs fA fB fC shift w := rfl
  have haCard : A.card≤(_root_.ThreeSum.BandRawA.items n g rs).length := by
    simpa only [Fintype.card_fin] using (Finset.card_le_univ A)
  have hbCard : B.card≤NB := by simpa only [Fintype.card_fin] using (Finset.card_le_univ B)
  have hcCard : C.card≤NC := by simpa only [Fintype.card_fin] using (Finset.card_le_univ C)
  have hcapacity := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout.capacity_le (shift := shift) A B C a b c w
    (by exact_mod_cast hp) hguard haCard hbCard hcCard
  have hgeo := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout.make_bounds (root := _root_.ThreeSum.ReportingHostWantedLayout.root dst J)
    (K := K) (W := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (G := _root_.ThreeSum.LocalCoverBounds.groupSize h)
    (T := 2^(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J)) hcapacity
  change _root_.ThreeSum.ReportingHostWantedLayout.Bounds L (_root_.ThreeSum.ReportingHostWantedLayout.root dst J) K (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J)
    (_root_.ThreeSum.LocalCoverBounds.groupSize h) (2^(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J)) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.capacity I w) at hgeo
  have hterminal := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout.terminal_count_le h J K
  have hdepth := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_depth (shift := shift) A B C a b c w hKJ (by exact_mod_cast hp) hguard haCard hbCard hcCard hd
  have hd' : d<lim.depth := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedDepth at hd
    omega
  have hsource := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.sources (fA := fA) (pair := pair) (cover := cover) (srcB := srcB) (srcC := srcC)
    (report := report) w HB hi hj houtput he
  have hcatalog (k : ℕ) (hk : k≤K) := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.catalog (fA := fA) (pair := pair) (bank := bank) (cover := cover)
    (occ := occ) (srcB := srcB) (srcC := srcC) w HQ hi hj houtput he
    (show k<_root_.ThreeSum.SharedReportingBankHeader.levels J by unfold _root_.ThreeSum.SharedReportingBankHeader.levels; omega) (hk.trans hKJ)
  have hcatBounds := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_catalog_bounds (pair := pair) (cover := cover) (occ := occ)
    hi hj (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode.source_code_lt h J output) hK hbank hreport
  have hmeta : ∀ k≤K, _root_.ThreeSum1960614.Machine.Light.SegN μ (S.catalog+5*k) ((D k).record h k) := fun k hk => (hcatalog k hk).1
  have hcatStored : ∀ (k : ℕ) (hk : k≤K),
      _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Stored μ (D k) (hk.trans hKJ) (p : ℤ) shift B C b c w.2.2 :=
    fun k hk => (hcatalog k hk).2
  have hcatBounds' : ∀ k≤K, _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Bounds h J k (D k) S.baseL S.baseR counter := hcatBounds.2
  have hmetaEnd : S.catalog+5*(K+1)≤counter := hcatBounds.1
  have hraw := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.raw_rows (w := w) hdecoded he
  have hscalars := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.cover_scalars HC
  have hbuckets := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.buckets (fA := fA) (bank := bank) (cover := cover)
    (occ := occ) (srcB := srcB) (srcC := srcC) (report := report) (output := output) w HP hi hj
  have hcoverInput := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.cover_input (fA := fA) (NB := NB) (NC := NC)
    (pair := pair) (bank := bank) (occ := occ) (srcB := srcB) (srcC := srcC)
    (report := report) (output := output) w HC
  have hreads := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.source_reads (pair := pair) (bank := bank) (cover := cover) (h := h) (J := J)
    (occ := occ) (report := report) (output := output) (fA := fA) w hg hi hj hreadB hreadC
  have hv : S.av=a w.1 := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.selected_value fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
  have hcounts : S.NL=_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.leftCount rs NB w ∧ S.NR=_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.rightCount rs NC w := ⟨rfl,rfl⟩
  have ha : |a w.1|≤lim.word := by
    rw [← hv]
    exact hselectedWords S.av (by simp only [_root_.ThreeSum.ReportingHostWantedControls.record,List.mem_cons]; exact Or.inl rfl)
  have hlocalB (j : ℕ) (hj' : j<S.NL) : _root_.ThreeSum.BandPartition.start g (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).b+j<NB :=
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.input_index hg hi hj'
  have hlocalC (j : ℕ) (hj' : j<S.NR) : _root_.ThreeSum.BandPartition.start g (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).c+j<NC :=
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.input_index hg hj hj'
  have hcountL : S.NL≤NB := (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.len_le_cap NB g _).trans (min_le_left _ _)
  have hcountR : S.NR≤NC := (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.len_le_cap NC g _).trans (min_le_left _ _)
  have hcountLocal : ((S.NL*S.NR : ℕ) : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (Nat.mul_le_mul hcountL hcountR)).trans hcountWord
  have hoccEnd : S.occ+J≤counter := hends.occurrence
  have hreportRun := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWanted.program_meets (μ := μ) (d := d+1)
    (srcL := S.srcL) (srcR := S.srcR) (offsetsL := S.offsetsL) (offsetsR := S.offsetsR)
    (flatL := S.flatL) (flatR := S.flatR) (NL := S.NL) (NR := S.NR) (occ := S.occ)
    (maps := S.maps) (candidates := S.candidates) (histL := S.histL) (histR := S.histR)
    (root := L.root) (catalogs := S.catalog) (rawRows := _root_.ThreeSum.ReportingHostWantedControls.rawRows dst J) (rows := _root_.ThreeSum.ReportingHostWantedLayout.packed dst J)
    (cover := cover) (counter := counter) (baseL := S.baseL) (baseR := S.baseR)
    (masks := L.masks) (childL := L.childL) (childR := L.childR) (counts := L.counts)
    (selected := L.selected) (maskBase := L.maskBase) (work := L.work)
    (terminalMasks := L.terminalMasks) (masksL := L.masksL) (masksR := L.masksR)
    (base := L.base) (bitBase := L.bitBase) (rowOut := L.rowOut)
    p shift (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.left rs fB w) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.right rs fC w) A B C a b c w D hKJ
    ⟨_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.mem_owner rs w,hkey⟩ hw hsource hcatStored hcatBounds' hqueries hmeta hmetaEnd
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls.rawRows_before_packed dst J) (by change _root_.ThreeSum.ReportingHostWantedLayout.packed dst J+J≤_root_.ThreeSum.ReportingHostWantedLayout.root dst J; rfl)
    (by unfold _root_.ThreeSum.ReportingHostWantedControls.rawRows _root_.ThreeSum.ReportingHostWantedLayout.decoded; omega) hscalars.1 (by have hh := hends.coverHeader; omega)
    hraw hcounterRead hthreshold hguardWord
    hgeo.frontier hgeo.masks hgeo.childL hgeo.childR hgeo.counts hgeo.selected
    hbuffers.parameters hbuffers.pack hbuckets.1 hbuckets.2
    hends.sourceL hends.sourceR hends.offsetsL hends.offsetsR hends.flatL hends.flatR
    (by unfold _root_.ThreeSum.ReportingHostWantedLayout.packed _root_.ThreeSum.ReportingHostWantedLayout.access _root_.ThreeSum.ReportingHostWantedLayout.decoded; omega)
    (Or.inr hends.occurrence) hends.maps hends.candidates hends.histL hends.histR
    hgeo.terminalFrontier
    ((Nat.add_le_add_left hterminal _).trans hgeo.terminalMasks)
    ((Nat.add_le_add_left hterminal _).trans hgeo.masksL)
    ((Nat.add_le_add_left hterminal _).trans hgeo.masksR)
    ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout.terminal_stop_mono hterminal).trans hgeo.stop) hgeo.bits hgeo.rowOut
    hbuffers.terminal hword (fun j hj' => _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedRecordData.occurrences (fA := fA) (pair := pair) (cover := cover)
      (srcB := srcB) (srcC := srcC) (report := report) w HB houtput he hj')
    hcoverInput hreads.1 hreads.2 (fun j hj' => hvaluesB _ (hlocalB j hj'))
    (fun j hj' => hvaluesC _ (hlocalC j hj')) ha (fun j hj' => htarget _ (hlocalB j hj'))
    hcountLocal (by omega)
  have hreportCall : _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWanted.program 137 (d+1)
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls.arguments S L dst cover counter h J K) μ
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWanted.time p shift (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.left rs fB w) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.right rs fC w)
        S.NL S.NR old threshold I w D K)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ threshold<old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w ∨
          _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.Terminal h J n NB NC g p rs fA fB fC shift w K) ∧
        ν counter=((old+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w : ℕ) : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν (_root_.ThreeSum.ReportingHostWantedLayout.packed dst J) counter 1) := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedControls.arguments,hv,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.Terminal,← hI,← hcounts.1,← hcounts.2,a] using hreportRun
  exact _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecordCall.program_meets hselected hlayout hscalars.2.1 hscalars.2.2
    hw hd' hrecordSpace hselectedWords hbuffers.values hreportCall
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecord.program_meets__implementation_2500f96b4b) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingWantedRecord.program_meets__implementation_2500f96b4b)

#print axioms solution
