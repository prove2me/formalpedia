-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostDecision.accepted_iff_witness
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:08:00.662275+00:00
-- url     : https://prove2.me/submissions/6e206731-94a9-4ae1-bee8-0960f443e569

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
import Theorems.Thm_ThreeSum_DenseGuardWanted_pair_indices_injective
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_RawIncidences_dense_early_yes
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_ReportingHostFrontier_mem_frontier_iff
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_ReportingHostTerminalBatch_hit_of_compatible
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_StoredReporting_positivePrefix_valid
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_ThreeSumWantedHostConditions_actual_separation
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_WantedRecordCoverage_output_complete
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_WantedRecordOrder_label_injective
import Theorems.Thm_ThreeSum_Arithmetic_small_lift_exists
import Theorems.Thm_ThreeSum_BandRawA_mem_aIndices_iff_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_allProducts
import Theorems.Thm_ThreeSum_BandRawA_mem_row
import Theorems.Thm_ThreeSum_BandRawA_product_values_mem
import Theorems.Thm_ThreeSum_BandRawA_relevant_product_complete
import Theorems.Thm_ThreeSum_Cover_greedy_cover
import Theorems.Thm_ThreeSum_LocalCoverBounds_pow_le_choose_mul
import Theorems.Thm_ThreeSum_LocalHashMoments_cover_frequency
import Theorems.Thm_ThreeSum_Radix_mem_representations

local instance platformRadixNonzero_079a9e0f93 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Filter
end Filter
namespace Finset
end Finset
namespace Light
end Light
namespace Real
end Real
namespace ThreeSum
end ThreeSum
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandPrimeChoice
end ThreeSum.BandPrimeChoice
namespace ThreeSum.BandPrimeScales
end ThreeSum.BandPrimeScales
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BandWeightedScore
end ThreeSum.BandWeightedScore
namespace ThreeSum.Bands
end ThreeSum.Bands
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.DenseGuard
end ThreeSum.DenseGuard
namespace ThreeSum.DenseGuardBands
end ThreeSum.DenseGuardBands
namespace ThreeSum.DenseGuardWanted
end ThreeSum.DenseGuardWanted
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorPrimeCosts
end ThreeSum.EncodedColorPrimeCosts
namespace ThreeSum.EncodedColorPrimeReadyData
end ThreeSum.EncodedColorPrimeReadyData
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LayerCounts
end ThreeSum.LayerCounts
namespace ThreeSum.LightBandPrimeConstruction
end ThreeSum.LightBandPrimeConstruction
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightMinimum
end ThreeSum.LightMinimum
namespace ThreeSum.LightPrimePool
end ThreeSum.LightPrimePool
namespace ThreeSum.LightReportingTerminalMasks
end ThreeSum.LightReportingTerminalMasks
namespace ThreeSum.LightReportingWantedScan
end ThreeSum.LightReportingWantedScan
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.Radix
end ThreeSum.Radix
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostPositive
end ThreeSum.ReportingHostPositive
namespace ThreeSum.ReportingHostTerminalBatch
end ThreeSum.ReportingHostTerminalBatch
namespace ThreeSum.ReportingHostTerminalOriginal
end ThreeSum.ReportingHostTerminalOriginal
namespace ThreeSum.ReportingHostWantedConsumerData
end ThreeSum.ReportingHostWantedConsumerData
namespace ThreeSum.ReportingHostWantedDecision
end ThreeSum.ReportingHostWantedDecision
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum.ReportingHostWantedPhysical
end ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum.ReportingHostWantedPrefix
end ThreeSum.ReportingHostWantedPrefix
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.ThreeSumWantedHostConditions
end ThreeSum.ThreeSumWantedHostConditions
namespace ThreeSum.ThreeSumWantedHostDecision
end ThreeSum.ThreeSumWantedHostDecision
namespace ThreeSum.WantedRecordOrder
end ThreeSum.WantedRecordOrder
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
end ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BandEnumeration
end ThreeSum1960614.Machine.ThreeSum.BandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice
end ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice
namespace ThreeSum1960614.Machine.ThreeSum.BandPrimeScales
end ThreeSum1960614.Machine.ThreeSum.BandPrimeScales
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.BandWeightedScore
end ThreeSum1960614.Machine.ThreeSum.BandWeightedScore
namespace ThreeSum1960614.Machine.ThreeSum.Bands
end ThreeSum1960614.Machine.ThreeSum.Bands
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.ColorClassLists
end ThreeSum1960614.Machine.ThreeSum.ColorClassLists
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.DenseGuard
end ThreeSum1960614.Machine.ThreeSum.DenseGuard
namespace ThreeSum1960614.Machine.ThreeSum.DenseGuardBands
end ThreeSum1960614.Machine.ThreeSum.DenseGuardBands
namespace ThreeSum1960614.Machine.ThreeSum.DenseGuardWanted
end ThreeSum1960614.Machine.ThreeSum.DenseGuardWanted
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
end ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts
end ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LayerCounts
end ThreeSum1960614.Machine.ThreeSum.LayerCounts
namespace ThreeSum1960614.Machine.ThreeSum.LightBandPrimeConstruction
end ThreeSum1960614.Machine.ThreeSum.LightBandPrimeConstruction
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
end ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
namespace ThreeSum1960614.Machine.ThreeSum.LightMinimum
end ThreeSum1960614.Machine.ThreeSum.LightMinimum
namespace ThreeSum1960614.Machine.ThreeSum.LightPrimePool
end ThreeSum1960614.Machine.ThreeSum.LightPrimePool
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
end ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScan
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScan
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.Radix
end ThreeSum1960614.Machine.ThreeSum.Radix
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest
end ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
end ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch
end ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
end ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalOriginal
end ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalOriginal
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedDecision
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedDecision
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
end ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions
end ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
end ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostDecision
end ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostDecision
namespace ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder
end ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder

namespace ThreeSum1960614.Machine

/-!
# The quadratic cardinal bound for relevant sorted-band triples

The proof is an explicit injection.  A relevant A interval either contains
the lower endpoint of a B/C difference interval, or its own lower endpoint
cuts that rectangle.  For a fixed cut, interval intersections inject into
the endpoints of the two families.

This file proves the combinatorial output bound and solution coverage.
It does not assign that bound to a cubic filtering implementation.
-/

namespace ThreeSum.Bands
open _root_.ThreeSum.Bands


variable {I J K : Type*}



























/-- Every exact equation in the input interval hulls survives band filtering. -/
theorem exact_equation_relevant
    {alo ahi : I → ℤ} {blo bhi : J → ℤ} {clo chi : K → ℤ}
    {i : I} {j : J} {k : K} {a b c : ℤ}
    (ha : alo i ≤ a ∧ a ≤ ahi i) (hb : blo j ≤ b ∧ b ≤ bhi j)
    (hc : clo k ≤ c ∧ c ≤ chi k) (heq : a + b = c) :
    _root_.ThreeSum.Bands.Relevant alo ahi blo bhi clo chi (i, j, k) := by
  constructor <;> dsimp only <;> omega

end ThreeSum.Bands

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact counts for the local subset graph

These are counts of the executable finite sets used by the graph, rather
than abstract numerical cardinality hypotheses.  An edge is an ordered
pair of disjoint `h`-subsets of `Fin L`.
-/

namespace ThreeSum.LayerCounts
open _root_.ThreeSum.LayerCounts


open _root_.Finset

















theorem vertex_degree_identity (L h : ℕ) :
    L.choose h * (L - h).choose h = L.choose (2 * h) * (2 * h).choose h := by
  simpa [show 2 * h - h = h by omega] using
    (Nat.choose_mul (n := L) (k := 2 * h) (s := h) (by omega)).symm



end ThreeSum.LayerCounts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A finite array minimum scan in the benchmark language

The selected index is a deterministic left-to-right minimum. Its value
can therefore instantiate the exact mean bound for offset balancing.
-/

namespace ThreeSum.LightMinimum
open _root_.ThreeSum.LightMinimum


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light



theorem least_lt (f : ℕ → ℤ) {n : ℕ} (hn : 0 < n) : _root_.ThreeSum.LightMinimum.least f n < n := by
  induction n with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero => simp [_root_.ThreeSum.LightMinimum.least]
      | succ n =>
          have h := ih (by omega)
          unfold _root_.ThreeSum.LightMinimum.least
          split <;> omega











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



end ThreeSum.LightMinimum

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Executing the candidate prime pool

This fixed program scans the integers in `(y,4*y]`, invokes the concrete
trial-division procedure, and writes every prime exactly once in increasing
order. The returned length and written array are the exact candidate pool
used by the contraction and auxiliary-weight theorems.
-/

namespace ThreeSum.LightPrimePool
open _root_.ThreeSum.LightPrimePool


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000



























theorem prime_spec {y i : ℕ} (hi : i < _root_.ThreeSum.LightPrimePool.size y) :
    Nat.Prime (_root_.ThreeSum.LightPrimePool.prime y i) ∧ y < _root_.ThreeSum.LightPrimePool.prime y i ∧ _root_.ThreeSum.LightPrimePool.prime y i ≤ 4*y :=
  _root_.ThreeSum.LightPrimePool.mem_values.mp (_root_.ThreeSum.LightPrimePool.prime_mem hi)





theorem values_nonempty {y : ℕ} (hy : 0 < y) : _root_.ThreeSum.LightPrimePool.values y ≠ [] := by
  obtain ⟨p,hp,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul y hy.ne'
  have hmem : p ∈ _root_.ThreeSum.LightPrimePool.values y := _root_.ThreeSum.LightPrimePool.mem_values.mpr ⟨hp,hlo,by omega⟩
  intro heq
  simpa only [heq,List.not_mem_nil] using hmem

theorem size_pos {y : ℕ} (hy : 0 < y) : 0 < _root_.ThreeSum.LightPrimePool.size y :=
  List.length_pos_iff.mpr (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.values_nonempty hy)



















variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightPrimePool

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact radix composition of finite local covers

The recursion enumerates only representations of one supplied target pair.
The coverage and multiplicity proofs quantify over arbitrary integer targets;
no enumeration of the square of the global modulus is used in the definition.
-/

namespace ThreeSum.Radix
open _root_.ThreeSum.Radix


open _root_.Finset
open scoped _root_.BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]











/-- Every pair is globally covered if every local pair has a choice. -/
theorem representations_nonempty (p : ℤ) (left right : Ω → ℤ)
    (hcover : ∀ a b, (_root_.ThreeSum.Radix.localFiber p left right a b).Nonempty)
    (j : ℕ) (a b : ℤ) : (_root_.ThreeSum.Radix.representations p left right j a b).Nonempty := by
  induction j generalizing a b with
  | zero => exact singleton_nonempty _
  | succ j ih =>
    obtain ⟨ω, hω⟩ := hcover a b
    obtain ⟨xs, hxs⟩ := ih ((a - left ω) / p) ((b - right ω) / p)
    refine ⟨ω :: xs, ?_⟩
    exact mem_biUnion.mpr ⟨ω, hω, mem_image.mpr ⟨xs, hxs, rfl⟩⟩





end ThreeSum.Radix

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






















theorem index_lt_size {n g i : ℕ} (hi : i < n) : i/g < _root_.ThreeSum.BandPartition.size n g := by
  have hn : n ≠ 0 := by omega
  have hh := Nat.div_le_div_right (c := g) (show i ≤ n-1 by omega)
  simp only [_root_.ThreeSum.BandPartition.size,if_neg hn]
  omega

theorem index_bounds {n g i : ℕ} (hg : 0 < g) (hi : i < n) :
    _root_.ThreeSum.BandPartition.start g (i/g) ≤ i ∧ i < _root_.ThreeSum.BandPartition.stop n g (i/g) := by
  have hlo := Nat.div_mul_le_self i g
  have hmod := Nat.mod_lt i hg
  have hsum := Nat.mod_add_div i g
  unfold _root_.ThreeSum.BandPartition.start _root_.ThreeSum.BandPartition.stop
  constructor
  · exact hlo
  · have hh : i < (i/g+1)*g := by nlinarith
    omega





theorem covers (f : ℕ → ℤ) (n g : ℕ) (hg : 0 < g)
    (hs : ∀ i j, i < j → j < n → f i < f j) {i : ℕ} (hi : i < n) :
    let A := _root_.ThreeSum.BandPartition.family f n g hg hs
    A.lower (i/g) ≤ f i ∧ f i ≤ A.upper (i/g) := by
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.index_bounds hg hi
  have hib := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.index_lt_size (g := g) hi
  exact ⟨_root_.ThreeSum.BandPartition.monotone_of_strict hs hb.1 hi,
    _root_.ThreeSum.BandPartition.monotone_of_strict hs (by omega) (_root_.ThreeSum.BandPartition.stop_sub_one_lt hg hib)⟩

end ThreeSum.BandPartition

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Finite numerical bounds for the local cover

The graph degree bound follows from exact finite cardinalities: the degree
is no larger than the number of vertices, while vertices times degree equal
outputs times representations per output.  This avoids any approximation
of factorials.  The prime-interval and normalized first-moment estimates
are stated explicitly in terms of the concrete binomial coefficients.
-/

namespace ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LocalCoverBounds


open scoped _root_.BigOperators








theorem concrete_output_gt_pow {h : ℕ} (hh : 0 < h) :
    2 ^ (2 * h) < _root_.ThreeSum.LocalCoverBounds.outputCount (464 * h) h := by
  have hlo : 232 ^ (2 * h) ≤ _root_.ThreeSum.LocalCoverBounds.outputCount (464 * h) h := by
    simpa [_root_.ThreeSum.LocalCoverBounds.outputCount, show 232 * (2 * h) = 464 * h by omega] using
      _root_.ThreeSum.LocalCoverBounds.pow_le_choose_mul 232 (2 * h)
  exact ((Nat.pow_lt_pow_iff_left (by omega : 2 * h ≠ 0)).mpr (by decide)).trans_le hlo

theorem degree_le_vertices (L h : ℕ) : _root_.ThreeSum.LocalCoverBounds.degree L h ≤ _root_.ThreeSum.LocalCoverBounds.vertexCount L h :=
  Nat.choose_le_choose h (Nat.sub_le L h)

theorem vertices_mul_degree (L h : ℕ) :
    _root_.ThreeSum.LocalCoverBounds.vertexCount L h * _root_.ThreeSum.LocalCoverBounds.degree L h = _root_.ThreeSum.LocalCoverBounds.outputCount L h * _root_.ThreeSum.LocalCoverBounds.groupSize h :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LayerCounts.vertex_degree_identity L h

theorem groupSize_lt_pow {h : ℕ} (hh : 0 < h) : _root_.ThreeSum.LocalCoverBounds.groupSize h < 2 ^ (2 * h) :=
  Nat.choose_lt_two_pow _ _ (by omega)

theorem groupSize_le_pow (h : ℕ) : _root_.ThreeSum.LocalCoverBounds.groupSize h ≤ 2 ^ (2 * h) :=
  Nat.choose_le_two_pow _ _



/-- Exact strict version of the degree-square estimate needed to compare the
degree with the selected prime. -/
theorem degree_sq_lt_output_pow {L h : ℕ} (hh : 0 < h) (hL : 2 * h ≤ L) :
    _root_.ThreeSum.LocalCoverBounds.degree L h ^ 2 < _root_.ThreeSum.LocalCoverBounds.outputCount L h * 2 ^ (2 * h) := by
  have hM : 0 < _root_.ThreeSum.LocalCoverBounds.outputCount L h := Nat.choose_pos hL
  calc
    _root_.ThreeSum.LocalCoverBounds.degree L h ^ 2 = _root_.ThreeSum.LocalCoverBounds.degree L h * _root_.ThreeSum.LocalCoverBounds.degree L h := by rw [pow_two]
    _ ≤ _root_.ThreeSum.LocalCoverBounds.vertexCount L h * _root_.ThreeSum.LocalCoverBounds.degree L h :=
      Nat.mul_le_mul_right _ (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.degree_le_vertices L h)
    _ = _root_.ThreeSum.LocalCoverBounds.outputCount L h * _root_.ThreeSum.LocalCoverBounds.groupSize h := _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.vertices_mul_degree L h
    _ < _root_.ThreeSum.LocalCoverBounds.outputCount L h * 2 ^ (2 * h) :=
      Nat.mul_lt_mul_of_pos_left (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.groupSize_lt_pow hh) hM

theorem degree_lt_modulus {L h p : ℕ} (hh : 0 < h) (hL : 2 * h ≤ L)
    (hp : _root_.ThreeSum.LocalCoverBounds.outputCount L h * 2 ^ (2 * h) ≤ p ^ 2) : _root_.ThreeSum.LocalCoverBounds.degree L h < p := by
  have hs := (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.degree_sq_lt_output_pow hh hL).trans_le hp
  nlinarith

theorem groupSize_lt_modulus {L h p : ℕ}
    (hM : 2 ^ (2 * h) < _root_.ThreeSum.LocalCoverBounds.outputCount L h)
    (hp : _root_.ThreeSum.LocalCoverBounds.outputCount L h * 2 ^ (2 * h) ≤ p ^ 2) : _root_.ThreeSum.LocalCoverBounds.groupSize h < p := by
  have hG := _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.groupSize_le_pow h
  have hpow : 0 < (2 : ℕ) ^ (2 * h) := Nat.pow_pos (by decide)
  have hsq : _root_.ThreeSum.LocalCoverBounds.groupSize h ^ 2 < _root_.ThreeSum.LocalCoverBounds.outputCount L h * 2 ^ (2 * h) := by
    calc
      _root_.ThreeSum.LocalCoverBounds.groupSize h ^ 2 ≤ (2 ^ (2 * h)) ^ 2 := Nat.pow_le_pow_left hG _
      _ = 2 ^ (2 * h) * 2 ^ (2 * h) := by rw [pow_two]
      _ < _root_.ThreeSum.LocalCoverBounds.outputCount L h * 2 ^ (2 * h) := Nat.mul_lt_mul_of_pos_right hM hpow
  have hs := hsq.trans_le hp
  nlinarith









/-! ## A deterministic selected prime -/































/-! ## Exact integer rounding of the separable bucket cap -/













/-! ## The actual local parameters at `L=464*h` -/



















theorem degree_lt_localPrime {h : ℕ} (hh : 0 < h) :
    _root_.ThreeSum.LocalCoverBounds.degree (464 * h) h < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.degree_lt_modulus hh (by omega) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_sq_lower h)

theorem groupSize_lt_localPrime {h : ℕ} (hh : 0 < h) : _root_.ThreeSum.LocalCoverBounds.groupSize h < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.groupSize_lt_modulus (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.concrete_output_gt_pow hh) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_sq_lower h)

theorem edgeCount_le_localPrime_sq (h : ℕ) :
    _root_.ThreeSum.LocalCoverBounds.outputCount (464 * h) h * _root_.ThreeSum.LocalCoverBounds.groupSize h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ^ 2 :=
  (Nat.mul_le_mul_left _ (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.groupSize_le_pow h)).trans (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_sq_lower h)











end ThreeSum.LocalCoverBounds

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



































theorem mem_allWeights (values : List K) (hvalues : ∀ x, x ∈ values)
    (w : _root_.ThreeSum.LocalHashMoments.Weight L K) : w ∈ _root_.ThreeSum.LocalHashMoments.allWeights L values := by
  apply List.mem_map.mpr
  refine ⟨(fun i _ => w i), ?_, rfl⟩
  exact (List.mem_pi _ _).mpr (fun i hi => hvalues (w i))







/-- The deterministic, actually defined schedule covers all ordered targets. -/
theorem schedule_covers (values : List K) (hvalues : ∀ x, x ∈ values)
    (hsep : 2 * h < L)
    (hDelta : _root_.ThreeSum.LocalCoverBounds.degree L h ≤ Fintype.card K)
    (hG : _root_.ThreeSum.LocalCoverBounds.groupSize h ≤ Fintype.card K)
    (hE : _root_.ThreeSum.LocalCoverBounds.outputCount L h * _root_.ThreeSum.LocalCoverBounds.groupSize h ≤ Fintype.card K ^ 2)
    (hupper : Fintype.card K ^ 2 ≤ 16 * (_root_.ThreeSum.LocalCoverBounds.outputCount L h * 2 ^ (2 * h)))
    (target : K × K) :
    ∃ w ∈ _root_.ThreeSum.LocalHashMoments.schedule L h values,
      _root_.ThreeSum.LocalHashMoments.Covers L h (_root_.ThreeSum.LocalHashMoments.bucketBound L h (Fintype.card K)) w target := by
  have hfreq : ∀ u ∈ (univ : Finset (K × K)), Fintype.card (_root_.ThreeSum.LocalHashMoments.Weight L K) ≤
      (320 * (2 * h + 1)) * (univ.filter fun w =>
        _root_.ThreeSum.LocalHashMoments.Covers L h (_root_.ThreeSum.LocalHashMoments.bucketBound L h (Fintype.card K)) w u).card := by
    intro u hu
    exact _root_.ThreeSum.LocalHashMoments.cover_frequency hsep hDelta hG hE hupper u
  have hc := _root_.ThreeSum.Cover.greedy_cover (_root_.ThreeSum.LocalHashMoments.allWeights L values) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.mem_allWeights values hvalues)
    (_root_.ThreeSum.LocalHashMoments.Covers L h (_root_.ThreeSum.LocalHashMoments.bucketBound L h (Fintype.card K)))
    (univ : Finset (K × K)) (320 * (2 * h + 1)) (by omega) hfreq target (mem_univ _)
  simpa only [_root_.ThreeSum.LocalHashMoments.schedule, _root_.ThreeSum.LocalHashMoments.scheduleLength, Finset.card_univ, Fintype.card_prod, pow_two] using hc

theorem cover_has_edge {B : ℕ} {w : _root_.ThreeSum.LocalHashMoments.Weight L K} {target : K × K}
    (hc : _root_.ThreeSum.LocalHashMoments.Covers L h B w target) :
    ∃ e : _root_.ThreeSum.LocalGraph.Edge L h, _root_.ThreeSum.HashFamily.hashValue w (_root_.ThreeSum.LocalGraph.left e) = target.1 ∧
      _root_.ThreeSum.HashFamily.hashValue w (_root_.ThreeSum.LocalGraph.right e) = target.2 ∧
      _root_.ThreeSum.HashFamily.bucketSize (_root_.ThreeSum.LocalGraph.leftVertices L h) w target.1 ≤ B ∧
      _root_.ThreeSum.HashFamily.bucketSize (_root_.ThreeSum.LocalGraph.rightVertices L h) w target.2 ≤ B := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc)
  have ht := (Finset.mem_filter.mp he).2
  have hp := (Finset.mem_filter.mp ht).1
  have hl := (Finset.mem_filter.mp ht).2
  exact ⟨e, (Finset.mem_filter.mp hp).2.1, (Finset.mem_filter.mp hp).2.2, hl⟩

/-! ## The selected local prime and its actual finite schedule -/







theorem mem_localValues (h : ℕ) (x : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) : x ∈ _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localValues h := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localValues
  have hv := List.mem_map_of_mem (f := fun n : ℕ => (n : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h))
    (List.mem_range.mpr x.val_lt)
  simpa only [ZMod.natCast_zmod_val] using hv





/-- Main concrete local-cover theorem. There are no moment, probability,
rank, prime-size, or coverage assumptions: the sole premise is `h>0`.
Every ordered residue pair, including an equal pair, is represented by a
retained edge under a member of the specified deterministic schedule. -/
theorem localSchedule_covers {h : ℕ} (hh : 0 < h) (target : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h × _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) :
    ∃ w ∈ _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule h, _root_.ThreeSum.LocalHashMoments.Covers (464 * h) h (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h) w target := by
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.schedule_covers (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localValues h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.mem_localValues h)
    (L := 464 * h) (h := h) (by omega)
    (by simpa only [ZMod.card] using (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.degree_lt_localPrime hh).le)
    (by simpa only [ZMod.card] using (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.groupSize_lt_localPrime hh).le)
    (by simpa only [ZMod.card] using _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.edgeCount_le_localPrime_sq h)
    (by simpa only [ZMod.card] using _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_sq_upper h) target
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule, _root_.ThreeSum.LocalHashMoments.bucketBound, _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap, ZMod.card] using hs

theorem localSchedule_represents {h : ℕ} (hh : 0 < h) (a b : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) :
    ∃ w ∈ _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule h, ∃ e : _root_.ThreeSum.LocalGraph.Edge (464 * h) h,
      _root_.ThreeSum.HashFamily.hashValue w (_root_.ThreeSum.LocalGraph.left e) = a ∧ _root_.ThreeSum.HashFamily.hashValue w (_root_.ThreeSum.LocalGraph.right e) = b ∧
      _root_.ThreeSum.HashFamily.bucketSize (_root_.ThreeSum.LocalGraph.leftVertices (464 * h) h) w a ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h ∧
      _root_.ThreeSum.HashFamily.bucketSize (_root_.ThreeSum.LocalGraph.rightVertices (464 * h) h) w b ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h := by
  obtain ⟨w, hw, hc⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule_covers hh (a, b)
  exact ⟨w, hw, _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.cover_has_edge hc⟩





end ThreeSum.LocalHashMoments

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The actual integer block schedule

All four size parameters below are executable natural-number functions.
The finite bounds and limits concern these functions, including the even
rounding of the cube root and the divisibility constraints on the number
of blocks.  No asymptotic size premise is imposed on the schedule.
-/

namespace ThreeSum.Scales
open _root_.ThreeSum.Scales


open _root_.Filter
open _root_.Real
open scoped _root_.Topology





















































noncomputable section

































































theorem primeDepth_upper (R : ℕ → ℕ) {n : ℕ} (hR : 4 ≤ R n) :
    4 * (4 * _root_.ThreeSum.Scales.primeWindow n) ^ _root_.ThreeSum.Scales.primeDepth R n ≤ R n := by
  have hr : R n / 4 ≠ 0 := by omega
  have h := Nat.pow_log_le_self (4 * _root_.ThreeSum.Scales.primeWindow n) hr
  have h4 := Nat.mul_le_mul_left 4 h
  have hd := Nat.div_mul_le_self (R n) 4
  simpa [_root_.ThreeSum.Scales.primeDepth, Nat.mul_comm] using h4.trans (by simpa [Nat.mul_comm] using hd)





































































end

end ThreeSum.Scales

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









section

private theorem private_b7a1750fd3_exists_list_index {α : Type*} (xs : List α) {n : ℕ}
    (hn : n = xs.length) (x : α) (hx : x ∈ xs) :
    ∃ i : Fin n, xs.get (Fin.cast hn i) = x := by
  subst n
  simpa only [Fin.cast_refl, id_eq] using List.mem_iff_get.mp hx
end


theorem mapAt_exists {h : ℕ} {w : _root_.ThreeSum.LocalHashMoments.Weight (464 * h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)}
    (hw : w ∈ _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule h) : ∃ i : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h i = w := by
  exact _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.private_b7a1750fd3_exists_list_index (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize_eq_length h) w hw














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

theorem localFiber_nonempty {h : ℕ} (hh : 0 < h) (a b : ℤ) :
    (_root_.ThreeSum.Radix.localFiber (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight a b : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h)).Nonempty := by
  obtain ⟨w, hw, e, ha, hb, hL, hR⟩ :=
    _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule_represents hh (a : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) (b : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)
  obtain ⟨i, hmap⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt_exists hw
  have hs : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Survives h i e := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Survives
    rw [hmap, ha, hb]
    exact ⟨hL, hR⟩
  refine ⟨⟨(i, e), hs⟩, (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mem_localFiber a b _).mpr ?_⟩
  change _root_.ThreeSum.HashFamily.hashValue (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h i) (_root_.ThreeSum.LocalGraph.left e) = (a : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) ∧
    _root_.ThreeSum.HashFamily.hashValue (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h i) (_root_.ThreeSum.LocalGraph.right e) = (b : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)
  rw [hmap]
  exact ⟨ha, hb⟩











theorem mem_representations (h J : ℕ) (a b : ℤ) (xs : List (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h)) :
    xs ∈ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representations h J a b ↔ xs.length = J ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ a - _root_.ThreeSum.Radix.positionalHash (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft xs ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ b - _root_.ThreeSum.Radix.positionalHash (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight xs := by
  exact _root_.ThreeSum.Radix.mem_representations (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)
    (by exact_mod_cast (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h).ne') _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight J a b xs

theorem representations_nonempty {h : ℕ} (hh : 0 < h) (J : ℕ) (a b : ℤ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representations h J a b).Nonempty :=
  _root_.ThreeSum1960614.Machine.ThreeSum.Radix.representations_nonempty (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight
    (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.localFiber_nonempty hh) J a b







theorem rawHash_difference {h L k : ℕ} (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h))
    (e : _root_.ThreeSum.LocalGraph.Edge L k) :
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash w (_root_.ThreeSum.LocalGraph.right e) - _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash w (_root_.ThreeSum.LocalGraph.left e) = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawOutput w (_root_.ThreeSum.LocalGraph.output e) := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawOutput
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hd := Finset.disjoint_left.mp (_root_.ThreeSum.LocalGraph.edge_data e).2.2
  by_cases hs : i ∈ e.val.1 <;> by_cases hv : i ∈ e.val.2 <;>
    simp_all [_root_.ThreeSum.LocalGraph.left, _root_.ThreeSum.LocalGraph.right, _root_.ThreeSum.LocalGraph.leftWord, _root_.ThreeSum.LocalGraph.rightWord, _root_.ThreeSum.LocalGraph.output]







theorem blockKey_choice {h : ℕ} (c : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h) :
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.blockKey (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.blockOfChoice c) = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight c - _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft c :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash_difference (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence c)) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge c)).symm









theorem positionalHash_difference {h : ℕ} (xs : List (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h)) :
    _root_.ThreeSum.Radix.positionalHash (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight xs -
      _root_.ThreeSum.Radix.positionalHash (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft xs =
        _root_.ThreeSum.Radix.positionalHash (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.blockKey (xs.map _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.blockOfChoice) := by
  induction xs with
  | nil => simp [_root_.ThreeSum.Radix.positionalHash]
  | cons c xs ih =>
      simp only [List.map_cons, _root_.ThreeSum.Radix.positionalHash, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.blockKey_choice]
      rw [← ih]
      ring











end ThreeSum.GlobalEncoding

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The exact physical band-owner record order

There is one four-cell record for every owner-table cell, in BC, AB, AC
rectangle order. A zero flag is a lookup miss. Successful records retain
their physical owner slot even when several owners produce the same triple.
-/

namespace ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandCandidateRows


open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000



























theorem rect_length (m n : ℕ) (F : ℕ → ℕ → _root_.ThreeSum.BandCandidateRows.Record) : (_root_.ThreeSum.BandCandidateRows.rect m n F).length=m*n := by
  simp [_root_.ThreeSum.BandCandidateRows.rect,List.length_flatMap]

theorem records_length (A B C : _root_.ThreeSum.BandEnumeration.Family) :
    (_root_.ThreeSum.BandCandidateRows.records A B C).length=_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size := by
  simp only [_root_.ThreeSum.BandCandidateRows.records,List.length_append,_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.rect_length,_root_.ThreeSum.LightBandEnumeration.count]
  omega



theorem index_lt {i j m n : ℕ} (hi : i < m) (hj : j < n) : i*n+j < m*n := by
  have hh := Nat.mul_le_mul_right n (show i+1 ≤ m by omega)
  simp only [Nat.add_mul,Nat.one_mul] at hh
  omega



theorem slot_lt (A B C : _root_.ThreeSum.BandEnumeration.Family) (o : _root_.ThreeSum.BandEnumeration.Owner A B C) :
    _root_.ThreeSum.BandCandidateRows.slot A B C o < _root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size := by
  rcases o with ⟨j,k⟩ | ⟨i,j | k⟩
  · have hh := _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.index_lt j.isLt k.isLt
    simp only [_root_.ThreeSum.BandCandidateRows.slot,_root_.ThreeSum.LightBandEnumeration.count]
    omega
  · have hh := _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.index_lt i.isLt j.isLt
    simp only [_root_.ThreeSum.BandCandidateRows.slot,_root_.ThreeSum.LightBandEnumeration.count]
    omega
  · have hh := _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.index_lt i.isLt k.isLt
    simp only [_root_.ThreeSum.BandCandidateRows.slot,_root_.ThreeSum.LightBandEnumeration.count]
    omega

















end ThreeSum.BandCandidateRows

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







theorem lift_complete {j : ℤ} (hj : _root_.ThreeSum.Arithmetic.SmallLift j) : ∃ i : Fin 3, _root_.ThreeSum.RawIncidences.lift i = j := by
  rcases hj with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩















theorem tupleKey_eq {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleKey t = _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleRight t - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleLeft t := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleKey, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey, _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleRight, _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleLeft, _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.positionalHash_difference]
  congr 1
  exact List.map_ofFn.symm













theorem ofFn_tupleOfList {h J : ℕ} (xs : List (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h)) (hlen : xs.length = J) :
    List.ofFn (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOfList xs hlen) = xs := by
  subst J
  exact List.ofFn_get xs

theorem tuple_mem_representations {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) (b c : ℤ) :
    List.ofFn t ∈ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representations h J b c ↔
      _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ b - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleLeft t ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ c - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleRight t := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mem_representations]
  simp only [List.length_ofFn, true_and, _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleLeft, _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleRight]

theorem tuple_difference_congruence {h J : ℕ} {t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J} {b c : ℤ}
    (ht : List.ofFn t ∈ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representations h J b c) :
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ (c - b) - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleKey t := by
  obtain ⟨hb, hc⟩ := (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tuple_mem_representations t b c).mp ht
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleKey_eq]
  rw [sub_sub_sub_comm]
  exact dvd_sub hc hb







theorem mem_witnesses {h J : ℕ} {P d a b c : ℤ} {w : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.Witness h J} :
    w ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses h J P d a b c ↔
      List.ofFn w.1 ∈ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representations h J (b % P) (c % P + d) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ (a % P + _root_.ThreeSum.RawIncidences.lift w.2 * P + d) - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleKey w.1 := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses, Finset.mem_filter, Finset.mem_univ, true_and]



theorem witnesses_nonempty {h J : ℕ} {P d a b c : ℤ}
    (hh : 0 < h) (hP : 0 < P) (hdiv : P ∣ c - b - a) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses h J P d a b c).Nonempty := by
  have heq : Int.ModEq P (c % P - b % P - a % P) (c - b - a) :=
    ((Int.mod_modEq c P).sub (Int.mod_modEq b P)).sub (Int.mod_modEq a P)
  have hnorm : P ∣ c % P - b % P - a % P := heq.dvd_iff.mpr hdiv
  obtain ⟨j, hj, he⟩ := _root_.ThreeSum.Arithmetic.small_lift_exists hP
    (Int.emod_nonneg _ hP.ne') (Int.emod_lt_of_pos _ hP)
    (Int.emod_nonneg _ hP.ne') (Int.emod_lt_of_pos _ hP)
    (Int.emod_nonneg _ hP.ne') (Int.emod_lt_of_pos _ hP) hnorm
  obtain ⟨l, hl⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.lift_complete hj
  obtain ⟨xs, hxs⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representations_nonempty hh J (b % P) (c % P + d)
  let hlen := ((_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mem_representations h J (b % P) (c % P + d) xs).mp hxs).1
  let t := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOfList xs hlen
  have ht : List.ofFn t ∈ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representations h J (b % P) (c % P + d) := by
    simpa only [t, _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ofFn_tupleOfList] using hxs
  refine ⟨(t, l), _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.mem_witnesses.mpr ⟨ht, ?_⟩⟩
  have hd := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tuple_difference_congruence ht
  have htarget : a % P + _root_.ThreeSum.RawIncidences.lift l * P + d = (c % P + d) - b % P := by
    rw [hl]
    linarith
  simpa only [htarget] using hd











section OriginalIndices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]









theorem mem_rawOn {h J : ℕ} {P d : ℤ} {T : Finset (_root_.ThreeSum.RawIncidences.Original α β γ)}
    {a : α → ℤ} {b : β → ℤ} {c : γ → ℤ} {r : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ} :
    r ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P d T a b c ↔
      r.1 ∈ T ∧ r.2 ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses h J P d (a r.1.1) (b r.1.2.1) (c r.1.2.2) :=
  Finset.mem_sigma



theorem raw_complete {h J : ℕ} {P d : ℤ} {T : Finset (_root_.ThreeSum.RawIncidences.Original α β γ)}
    {a : α → ℤ} {b : β → ℤ} {c : γ → ℤ} {t : _root_.ThreeSum.RawIncidences.Original α β γ}
    (hh : 0 < h) (hP : 0 < P) (ht : t ∈ T) (hd : P ∣ _root_.ThreeSum.RawIncidences.difference a b c t) :
    ∃ r ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P d T a b c, r.1 = t := by
  obtain ⟨w, hw⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses_nonempty hh hP hd
  exact ⟨⟨t, w⟩, _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.mem_rawOn.mpr ⟨ht, hw⟩, rfl⟩

































end OriginalIndices

end ThreeSum.RawIncidences

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A common contracting modulus for the complete band-owner catalog

The same deterministic first-minimum rule is applied to the sum of every
flagged owner's score. These are joint choices for all bands, rather than
independent moduli whose contractions could not be combined.
-/

namespace ThreeSum.BandPrimeChoice
open _root_.ThreeSum.BandPrimeChoice


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandWeightedScore
open _root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 1400000
set_option maxRecDepth 8000







theorem chosenIndex_lt (primes : ℕ → ℕ) {s q nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (hs : 0 < s) :
    _root_.ThreeSum.BandPrimeChoice.chosenIndex primes s q nA nB nC g A B C rs < s := _root_.ThreeSum1960614.Machine.ThreeSum.LightMinimum.least_lt _ hs







theorem modulus_bounds (primes : ℕ → ℕ) {s nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (hs : 0 < s) (y Y r : ℕ)
    (hlo : ∀ i < s, y ≤ primes i) (hhi : ∀ i < s, primes i ≤ Y) :
    y^r ≤ _root_.ThreeSum.BandPrimeChoice.modulus primes s nA nB nC g A B C rs r ∧
      _root_.ThreeSum.BandPrimeChoice.modulus primes s nA nB nC g A B C rs r ≤ Y^r := by
  induction r with
  | zero => simp [_root_.ThreeSum.BandPrimeChoice.modulus]
  | succ r ih =>
    have hidx := _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice.chosenIndex_lt (q := _root_.ThreeSum.BandPrimeChoice.modulus primes s nA nB nC g A B C rs r)
      (nA := nA) (nB := nB) (nC := nC) (g := g) primes A B C rs hs
    constructor
    · simpa only [_root_.ThreeSum.BandPrimeChoice.modulus,pow_succ,_root_.ThreeSum.BandPrimeChoice.chosenPrime] using Nat.mul_le_mul ih.1 (hlo _ hidx)
    · simpa only [_root_.ThreeSum.BandPrimeChoice.modulus,pow_succ,_root_.ThreeSum.BandPrimeChoice.chosenPrime] using Nat.mul_le_mul ih.2 (hhi _ hidx)

theorem modulus_pos (primes : ℕ → ℕ) {s nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (hs : 0 < s)
    (hprime : ∀ i < s, Nat.Prime (primes i)) (r : ℕ) :
    0 < _root_.ThreeSum.BandPrimeChoice.modulus primes s nA nB nC g A B C rs r := by
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice.modulus_bounds (nA := nA) (nB := nB) (nC := nC) (g := g) primes A B C rs hs 1
    (Finset.sup (range s) primes) r
    (fun i hi => (hprime i hi).pos)
    (fun i hi => Finset.le_sup (mem_range.mpr hi))).1
  rw [one_pow] at hh
  omega









end ThreeSum.BandPrimeChoice

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
# Exact next-frontier order and raw-mass charges for the actual expansion

Gathering the stably selected child positions produces exactly the recursive
reporting frontier, including its original order and retained multiplicity.
-/

namespace ThreeSum.ReportingHostPositive
open _root_.ThreeSum.ReportingHostPositive


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
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
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier
open scoped _root_.BigOperators

set_option linter.unusedSectionVars false





theorem frontier_positive {α : Type*} (children : ℕ → List α) (query : ℕ → List α → ℕ)
    {k : ℕ} {pre : List α} (hp : pre ∈ _root_.ThreeSum.Reporting.frontier children query k) :
    0 < query k pre := by
  cases k with
  | zero =>
      simp only [_root_.ThreeSum.Reporting.frontier] at hp
      split at hp
      · have he : pre = [] := List.mem_singleton.mp hp
        simpa only [he] using ‹0 < query 0 []›
      · cases hp
  | succ k =>
      exact of_decide_eq_true (List.mem_filter.mp hp).2

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]







theorem frontier_valid {h J k : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (hk : k ≤ J) {pre : List (Finset (Fin (464*h)))}
    (hp : pre ∈ _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k) : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix w.2.2 k pre :=
  _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.positivePrefix_valid I w pre hk (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.frontier_positive _ _ hp)







end ThreeSum.ReportingHostPositive

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
# Construct the prime pool and common contracting modulus from band records

The fixed host constructs the candidate prime array, then executes the
aggregate modulus chain on every owner record. The physical prime array and
every prefix modulus remain available to the encoder and reporting stages.
-/

namespace ThreeSum.LightBandPrimeConstruction
open _root_.ThreeSum.LightBandPrimeConstruction


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000



theorem modulus_bounds {y nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (levels : ℕ) (hy : 0 < y) :
    y^levels ≤ _root_.ThreeSum.LightBandPrimeConstruction.modulus y nA nB nC g A B C rs levels ∧
      _root_.ThreeSum.LightBandPrimeConstruction.modulus y nA nB nC g A B C rs levels ≤ (4*y)^levels :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice.modulus_bounds (_root_.ThreeSum.LightPrimePool.prime y) A B C rs
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.size_pos hy) y (4*y) levels
    (fun i hi => (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_spec hi).2.1.le)
    (fun i hi => (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_spec hi).2.2)















variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs y levels free maxMod U : ℕ}



end ThreeSum.LightBandPrimeConstruction

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

/-!
# Exact original-encoding semantics and cost of the executed terminal batch

This is the specialization of the actual seven-procedure batch to the full
endpoint masks emitted at a valid partial prefix. The precise ordered
candidate sum is charged to raw prefix mass plus the terminal cube term.
-/

namespace ThreeSum.ReportingHostTerminalBatch
open _root_.ThreeSum.ReportingHostTerminalBatch


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBlockBucketTest
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.LightSourceResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
open _root_.ThreeSum.LightReportingTerminalMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
open scoped _root_.BigOperators

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false














variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]



theorem hit_sound {h J k NL NR : ℕ} {av shift : ℤ} {p : ℕ} {left right : ℕ→ℤ}
    {q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J} {pre : List (Finset (Fin (464*h)))}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.Hit av p shift left right NL NR q k pre) :
    ∃ i<NL, ∃ j<NR, right j-left i-av=0 := by
  obtain ⟨s,hs,_,_,i,hi,j,hj,_,_,he⟩ := H
  exact ⟨i,hi,j,hj,he⟩



end ThreeSum.ReportingHostTerminalBatch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Each physical A incidence retains exactly its owner's B/C product

The products in this file are mathematical counting domains. The actual
catalog is still constructed by the verified quadratic owner loop and
linear band copies. Distinct owner products are disjoint because their
physical A incidence indices differ, even when their values coincide.
-/

namespace ThreeSum.BandRawA
open _root_.ThreeSum.BandRawA


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 1900000
set_option maxRecDepth 8000



















theorem mem_ownerProduct {nA nB nC g s : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record} {t : ℕ × ℕ × ℕ}
    (hs : s < rs.length) :
    t ∈ _root_.ThreeSum.BandRawA.ownerProduct nA nB nC g rs s ↔
      t.1 < (_root_.ThreeSum.BandRawA.items nA g rs).length ∧ (_root_.ThreeSum.BandRawA.labelAt nA g rs t.1).owner=s ∧
        t.2.1 ∈ _root_.ThreeSum.BandRawA.bandPositions nB g (rs.getD s default).b ∧
        t.2.2 ∈ _root_.ThreeSum.BandRawA.bandPositions nC g (rs.getD s default).c := by
  simp only [_root_.ThreeSum.BandRawA.ownerProduct,mem_product,_root_.ThreeSum.BandRawA.mem_aIndices_iff_owner hs,and_assoc]















end ThreeSum.BandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Sound cumulative dense stopping on visited wanted labels

Distinct wanted labels have disjoint raw-incidence fibers. Therefore any
visited prefix already exceeding the exact representation-times-false-score
threshold certifies an original equation, before proportional traversal.
-/

namespace ThreeSum.DenseGuard
open _root_.ThreeSum.DenseGuard


open _root_.Finset
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]



@[simp] theorem mass_nil {h J : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) : _root_.ThreeSum1960614.Machine.ThreeSum.DenseGuard.mass I []=0 := rfl

theorem mass_append {h J : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ))
    (visited : List (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) :
    _root_.ThreeSum1960614.Machine.ThreeSum.DenseGuard.mass I (visited++[w])=_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuard.mass I visited+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w := by simp [_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuard.mass]

theorem mass_le_raw_card {h J : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ))
    (visited : List (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)) (hn : visited.Nodup) : _root_.ThreeSum1960614.Machine.ThreeSum.DenseGuard.mass I visited ≤ I.card := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.DenseGuard.mass
  rw [← List.sum_toFinset _ hn]
  calc
    _ ≤ ∑ w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α, _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass I w := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = I.card := by
      simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass_eq]
      symm
      exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)

theorem partial_early_yes {h J : ℕ} {P d : ℤ} (T : Finset (_root_.ThreeSum.RawIncidences.Original α β γ))
    (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (aux : Finset ℤ)
    (visited : List (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)) (hn : visited.Nodup)
    (hP : 0 < P) (hguard : 4*P ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J)
    (hsep : ∀ t ∈ T, _root_.ThreeSum.RawIncidences.difference a b c t ≠ 0 → ∃ l ∈ aux, ¬ l ∣ _root_.ThreeSum.RawIncidences.difference a b c t)
    (hlarge : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J*_root_.ThreeSum.Arithmetic.weightedFalseCount T (_root_.ThreeSum.RawIncidences.difference a b c) aux P <
      _root_.ThreeSum1960614.Machine.ThreeSum.DenseGuard.mass (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P d T a b c) visited) :
    ∃ t ∈ T, _root_.ThreeSum.RawIncidences.difference a b c t=0 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.dense_early_yes T a b c aux hP hguard hsep
    (hlarge.trans_le (_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuard.mass_le_raw_card _ visited hn))

theorem partial_early_yes_of_upper {h J H : ℕ} {P d : ℤ}
    (T : Finset (_root_.ThreeSum.RawIncidences.Original α β γ)) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (aux : Finset ℤ)
    (visited : List (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)) (hn : visited.Nodup)
    (hP : 0 < P) (hguard : 4*P ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J)
    (hsep : ∀ t ∈ T, _root_.ThreeSum.RawIncidences.difference a b c t ≠ 0 → ∃ l ∈ aux, ¬ l ∣ _root_.ThreeSum.RawIncidences.difference a b c t)
    (hH : _root_.ThreeSum.Arithmetic.weightedFalseCount T (_root_.ThreeSum.RawIncidences.difference a b c) aux P ≤ H)
    (hlarge : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J*H < _root_.ThreeSum1960614.Machine.ThreeSum.DenseGuard.mass (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P d T a b c) visited) :
    ∃ t ∈ T, _root_.ThreeSum.RawIncidences.difference a b c t=0 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.DenseGuard.partial_early_yes T a b c aux visited hn hP hguard hsep
    ((Nat.mul_le_mul_left _ hH).trans_lt hlarge)



end ThreeSum.DenseGuard

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original raw witnesses reach the actually tested terminal prefixes

Every true raw incidence has a stored positive prefix at any chosen partial
depth, and its retained completion appears in the actual terminal batch.
Conversely, every positive terminal result supplies an original finite
owner-domain triple whose integer values satisfy the exact equation.
-/

namespace ThreeSum.ReportingHostTerminalOriginal
open _root_.ThreeSum.ReportingHostTerminalOriginal


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem hit_of_raw {h J k NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (pre : List (Finset (Fin (464*h)))) (hk : k≤J) (hp : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix w.2.2 k pre)
    (r : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ) (hr : r∈_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c)
    (hw : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.wantedOf r=w) (hpre : (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.word r).take k=pre) (hzero : _root_.ThreeSum.RawIncidences.difference a b c r.1=0) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.Hit (a w.1) p shift left right NL NR w.2.2 k pre := by
  have hq : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput r.2.1=w.2.2 := congrArg (fun w => w.2.2) hw
  have ha : r.1.1=w.1 := congrArg Prod.fst hw
  have hraw := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.mem_rawOn.mp hr
  have hrep := (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.mem_witnesses.mp hraw.2).1
  have hpair := (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tuple_mem_representations r.2.1 (b r.1.2.1%(p : ℤ))
    (c r.1.2.2%(p : ℤ)+shift)).mp hrep
  have hcompletion : r.2.1∈_root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.completions w.2.2 k pre :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq,hpre⟩
  have hcompatible : r.1.2∈_root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.compatiblePairs (p : ℤ) shift B C b c r.2.1 :=
    Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hraw.1).2,hpair⟩
  exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.hit_of_compatible p shift (a w.1) B C b c left right eL eR hvL hvR w.2.2 pre hk hp
    r.2.1 hcompletion r.1.2 hcompatible (by simpa only [_root_.ThreeSum.RawIncidences.difference,ha] using hzero)

theorem hit_sound_original {h J k NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (pre : List (Finset (Fin (464*h)))) (ha : w.1∈A)
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.Hit (a w.1) p shift left right NL NR w.2.2 k pre) :
    ∃ t∈A ×ˢ (B ×ˢ C), t.1=w.1 ∧ _root_.ThreeSum.RawIncidences.difference a b c t=0 := by
  obtain ⟨i,hi,j,hj,he⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.hit_sound H
  let u := eL ⟨i,hi⟩
  let v := eR ⟨j,hj⟩
  refine ⟨(w.1,u.val,v.val),Finset.mem_product.mpr ⟨ha,Finset.mem_product.mpr ⟨u.property,v.property⟩⟩,rfl,?_⟩
  change c v.val-b u.val-a w.1=0
  rw [← hvL ⟨i,hi⟩,← hvR ⟨j,hj⟩]
  exact he

theorem frontier_hit_of_raw {h J k NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) (hk : k≤J) (r : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)
    (hr : r∈_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c)
    (hw : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.wantedOf r=w) (hzero : _root_.ThreeSum.RawIncidences.difference a b c r.1=0) :
    ∃ pre∈_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w k,
      _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalBatch.Hit (a w.1) p shift left right NL NR w.2.2 k pre := by
  let I := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
  have hfront : (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.word r).take k∈_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.frontier I w k :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontier.mem_frontier_iff I w hk _).mpr ⟨r,hr,hw,rfl⟩
  refine ⟨(_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.word r).take k,hfront,?_⟩
  exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalOriginal.hit_of_raw p shift A B C a b c left right eL eR hvL hvR w _ hk
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPositive.frontier_valid I w hk hfront) r hr hw rfl hzero



end ThreeSum.ReportingHostTerminalOriginal

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Finite scale guarantees for the executed physical-owner modulus

These theorems instantiate the previously proved size-only mass bounds with
the common modulus actually constructed from the candidate record array.
The weighted count is over physical A incidences and their own B/C bands.
-/

namespace ThreeSum.BandPrimeScales
open _root_.ThreeSum.BandPrimeScales


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger

set_option maxHeartbeats 1600000
set_option maxRecDepth 9000









theorem modulus_bounds (n nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) :
    _root_.ThreeSum.Scales.primeWindow n^_root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.modulus n nA nB nC A B C rs ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.modulus n nA nB nC A B C rs ≤ (4*_root_.ThreeSum.Scales.primeWindow n)^_root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeConstruction.modulus_bounds A B C rs _ (by have := _root_.ThreeSum.Scales.primeWindow_ge_two n; omega)

/-- The integer guard used by the three-lift residue construction. -/
theorem modulus_guard {n nA nB nC : ℕ} (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (hR : 4 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) : 4*_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.modulus n nA nB nC A B C rs ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n :=
  (Nat.mul_le_mul_left 4 (_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.modulus_bounds n nA nB nC A B C rs).2).trans
    (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.primeDepth_upper _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix hR)















end ThreeSum.BandPrimeScales

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



@[simp] theorem mem_finiteOwnerProduct {nA nB nC g s : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record}
    {t : Fin (_root_.ThreeSum.BandRawA.items nA g rs).length × Fin nB × Fin nC} :
    t ∈ _root_.ThreeSum.BandRawA.finiteOwnerProduct nA nB nC g rs s ↔
      _root_.ThreeSum.BandRawA.coordinates t ∈ _root_.ThreeSum.BandRawA.ownerProduct nA nB nC g rs s := by
  simp only [_root_.ThreeSum.BandRawA.finiteOwnerProduct,_root_.ThreeSum.BandRawA.ownerProduct,mem_product,_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.mem_finiteAIndices,
    _root_.ThreeSum.BandRawA.mem_finiteBandPositions,_root_.ThreeSum.BandRawA.coordinates]

@[simp] theorem mem_finiteAllProducts {nA nB nC g : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record}
    {t : Fin (_root_.ThreeSum.BandRawA.items nA g rs).length × Fin nB × Fin nC} :
    t ∈ _root_.ThreeSum.BandRawA.finiteAllProducts nA nB nC g rs ↔
      _root_.ThreeSum.BandRawA.coordinates t ∈ _root_.ThreeSum.BandRawA.allProducts nA nB nC g rs := by
  simp only [_root_.ThreeSum.BandRawA.finiteAllProducts,mem_filter,mem_univ,true_and]

theorem finiteAIndices_owner {n g s : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record}
    (hs : s < rs.length) {i : Fin (_root_.ThreeSum.BandRawA.items n g rs).length} :
    i ∈ _root_.ThreeSum.BandRawA.finiteAIndices n g rs s ↔ (_root_.ThreeSum.BandRawA.labelAt n g rs i.val).owner=s := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.mem_finiteAIndices,_root_.ThreeSum.BandRawA.mem_aIndices_iff_owner hs]
  simp only [i.isLt,true_and]



theorem allProducts_bounds {nA nB nC g : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ _root_.ThreeSum.BandRawA.allProducts nA nB nC g rs) :
    t.1 < (_root_.ThreeSum.BandRawA.items nA g rs).length ∧ t.2.1 < nB ∧ t.2.2 < nC := by
  obtain ⟨ha,hb,hc⟩ := _root_.ThreeSum.BandRawA.mem_allProducts.mp ht
  exact ⟨ha,_root_.ThreeSum.BandRawA.bandPositions_lt hb,_root_.ThreeSum.BandRawA.bandPositions_lt hc⟩



theorem finite_lift {nA nB nC g : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ _root_.ThreeSum.BandRawA.allProducts nA nB nC g rs) :
    ∃ u ∈ _root_.ThreeSum.BandRawA.finiteAllProducts nA nB nC g rs, _root_.ThreeSum.BandRawA.coordinates u=t := by
  obtain ⟨ha,hb,hc⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.allProducts_bounds ht
  refine ⟨(⟨t.1,ha⟩,⟨t.2.1,hb⟩,⟨t.2.2,hc⟩),?_,rfl⟩
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.mem_finiteAllProducts.mpr ht













end ThreeSum.BandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact original-value membership and equation coverage of the owner catalog

Normalized sorted coordinates remain distinct from original input
positions. The normalization membership equivalence transfers values back
to their original color classes; the color-class bridge can then recover
the required distinct original positions.
-/

namespace ThreeSum.BandRawA
open _root_.ThreeSum.BandRawA


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000





theorem product_original_values {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record} {t : ℕ × ℕ × ℕ}
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ht : t ∈ _root_.ThreeSum.BandRawA.allProducts A.length B.length C.length g rs) :
    _root_.ThreeSum.BandRawA.valueAt A.length g rs (fun i => A.getD i 0) t.1 ∈ originalA ∧
      B.getD t.2.1 0 ∈ originalB ∧ C.getD t.2.2 0 ∈ originalC := by
  obtain ⟨ha,hb,hc⟩ := _root_.ThreeSum.BandRawA.product_values_mem ht
  exact ⟨(hA _).mp ha,(hB _).mp hb,(hC _).mp hc⟩

theorem sorted_equation_complete {A B C : List ℤ} {g : ℕ} {a b c : ℤ}
    (hg : 0 < g) (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·))
    (hsC : C.Pairwise (· < ·)) (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ C)
    (heq : a+b=c) :
    ∃ t ∈ _root_.ThreeSum.BandRawA.allProducts A.length B.length C.length g (_root_.ThreeSum.BandRawA.sortedRecords A B C g hg hsA hsB hsC),
      _root_.ThreeSum.BandRawA.valueAt A.length g (_root_.ThreeSum.BandRawA.sortedRecords A B C g hg hsA hsB hsC)
        (fun i => A.getD i 0) t.1=a ∧ B.getD t.2.1 0=b ∧ C.getD t.2.2 0=c := by
  obtain ⟨ia,hia,hA⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨ib,hib,hB⟩ := List.mem_iff_getElem.mp hb
  obtain ⟨ic,hic,hC⟩ := List.mem_iff_getElem.mp hc
  have hAget : A.getD ia 0=a := (List.getD_eq_getElem A 0 hia).trans hA
  have hBget : B.getD ib 0=b := (List.getD_eq_getElem B 0 hib).trans hB
  have hCget : C.getD ic 0=c := (List.getD_eq_getElem C 0 hic).trans hC
  let FA := _root_.ThreeSum.BandPartition.family (fun i => A.getD i 0) A.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hsA)
  let FB := _root_.ThreeSum.BandPartition.family (fun i => B.getD i 0) B.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hsB)
  let FC := _root_.ThreeSum.BandPartition.family (fun i => C.getD i 0) C.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hsC)
  let band : _root_.ThreeSum.BandEnumeration.Triple FA FB FC :=
    (⟨ia/g,_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.index_lt_size hia⟩,⟨ib/g,_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.index_lt_size hib⟩,⟨ic/g,_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.index_lt_size hic⟩)
  have hAband : FA.lo band.1 ≤ a ∧ a ≤ FA.hi band.1 := by
    simpa only [FA,band,_root_.ThreeSum.BandEnumeration.Family.lo,_root_.ThreeSum.BandEnumeration.Family.hi,hAget] using _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.covers (fun i => A.getD i 0) A.length g hg
      (_root_.ThreeSum.LightSortedBands.getD_strict hsA) hia
  have hBband : FB.lo band.2.1 ≤ b ∧ b ≤ FB.hi band.2.1 := by
    simpa only [FB,band,_root_.ThreeSum.BandEnumeration.Family.lo,_root_.ThreeSum.BandEnumeration.Family.hi,hBget] using _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.covers (fun i => B.getD i 0) B.length g hg
      (_root_.ThreeSum.LightSortedBands.getD_strict hsB) hib
  have hCband : FC.lo band.2.2 ≤ c ∧ c ≤ FC.hi band.2.2 := by
    simpa only [FC,band,_root_.ThreeSum.BandEnumeration.Family.lo,_root_.ThreeSum.BandEnumeration.Family.hi,hCget] using _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.covers (fun i => C.getD i 0) C.length g hg
      (_root_.ThreeSum.LightSortedBands.getD_strict hsC) hic
  have hrel : _root_.ThreeSum.BandEnumeration.relevant FA FB FC band := _root_.ThreeSum1960614.Machine.ThreeSum.Bands.exact_equation_relevant hAband hBband hCband heq
  have hap : _root_.ThreeSum.BandPartition.start g band.1.val ≤ ia ∧ ia < _root_.ThreeSum.BandPartition.stop A.length g band.1.val := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.index_bounds hg hia
  have hbp : _root_.ThreeSum.BandPartition.start g band.2.1.val ≤ ib ∧ ib < _root_.ThreeSum.BandPartition.stop B.length g band.2.1.val := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.index_bounds hg hib
  have hcp : _root_.ThreeSum.BandPartition.start g band.2.2.val ≤ ic ∧ ic < _root_.ThreeSum.BandPartition.stop C.length g band.2.2.val := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.index_bounds hg hic
  obtain ⟨k,hk,hlabel,hproduct⟩ := _root_.ThreeSum.BandRawA.relevant_product_complete band hrel hap hbp hcp
  have hs : _root_.ThreeSum.BandCandidateRows.slot FA FB FC (_root_.ThreeSum.BandEnumeration.owner FA FB FC band) < (_root_.ThreeSum.BandCandidateRows.records FA FB FC).length := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.records_length]
    exact _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.slot_lt FA FB FC _
  have hall : (k,ib,ic) ∈ _root_.ThreeSum.BandRawA.allProducts A.length B.length C.length g (_root_.ThreeSum.BandCandidateRows.records FA FB FC) :=
    mem_biUnion.mpr ⟨_root_.ThreeSum.BandCandidateRows.slot FA FB FC (_root_.ThreeSum.BandEnumeration.owner FA FB FC band),mem_range.mpr hs,hproduct⟩
  refine ⟨(k,ib,ic),hall,?_,hBget,hCget⟩
  change _root_.ThreeSum.BandRawA.valueAt A.length g (_root_.ThreeSum.BandCandidateRows.records FA FB FC) (fun i => A.getD i 0) k=a
  rw [_root_.ThreeSum.BandRawA.valueAt,_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.values_getD _ hk,hlabel]
  exact hAget

theorem original_equation_complete {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {a b c : ℤ} (hg : 0 < g)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·))
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ha : a ∈ originalA) (hb : b ∈ originalB) (hc : c ∈ originalC) (heq : a+b=c) :
    ∃ t ∈ _root_.ThreeSum.BandRawA.allProducts A.length B.length C.length g (_root_.ThreeSum.BandRawA.sortedRecords A B C g hg hsA hsB hsC),
      _root_.ThreeSum.BandRawA.valueAt A.length g (_root_.ThreeSum.BandRawA.sortedRecords A B C g hg hsA hsB hsC)
        (fun i => A.getD i 0) t.1=a ∧ B.getD t.2.1 0=b ∧ C.getD t.2.2 0=c :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.sorted_equation_complete hg hsA hsB hsC ((hA a).mpr ha) ((hB b).mpr hb) ((hC c).mpr hc) heq

theorem original_equation_sound {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record} {t : ℕ × ℕ × ℕ}
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ht : t ∈ _root_.ThreeSum.BandRawA.allProducts A.length B.length C.length g rs)
    (heq : _root_.ThreeSum.BandRawA.valueAt A.length g rs (fun i => A.getD i 0) t.1+B.getD t.2.1 0=C.getD t.2.2 0) :
    ∃ a ∈ originalA, ∃ b ∈ originalB, ∃ c ∈ originalC, a+b=c := by
  obtain ⟨ha,hb,hc⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.product_original_values hA hB hC ht
  exact ⟨_,ha,_,hb,_,hc,heq⟩

end ThreeSum.BandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Distinct wanted labels in the actual emitted array

The join's physical slots decode injectively, even when original integer
values or key values repeat. Consequently every prefix of the actual
array is a valid distinct-label input to the cumulative dense guard.
-/

namespace ThreeSum.DenseGuardWanted
open _root_.ThreeSum.DenseGuardWanted


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.WantedRecordOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder











theorem labelAt_injective {μ : ℕ → ℤ} {free M P h J : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output μ free M (_root_.ThreeSum.LightGuardedWanted.left P xs)
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right h J) (3*xs.length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) shift) :
    Function.Injective (_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardWanted.labelAt H) := by
  intro k k' he
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder.label_injective (_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardWanted.output_bounds H k.isLt).1 (_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardWanted.output_bounds H k'.isLt).1
    (_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardWanted.output_bounds H k.isLt).2 (_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardWanted.output_bounds H k'.isLt).2 he
  exact Fin.ext (_root_.ThreeSum.DenseGuardWanted.pair_indices_injective H k.isLt k'.isLt hp.1 hp.2)











theorem labels_complete {μ : ℕ → ℤ} {free M P h J : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output μ free M (_root_.ThreeSum.LightGuardedWanted.left P xs)
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right h J) (3*xs.length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) shift)
    {w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (Fin xs.length)}
    (hw : w ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.wanted M P xs h J shift) : w ∈ _root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardWanted.labels H := by
  obtain ⟨slot,i,j,hi,hk,_,hL,hR,he⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordCoverage.output_complete H hw
  apply List.mem_ofFn.mpr
  refine ⟨⟨slot,hk⟩,?_⟩
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardWanted.labelAt,_root_.ThreeSum.DenseGuardWanted.leftIndex,_root_.ThreeSum.DenseGuardWanted.rightIndex,hL,hR,Int.toNat_natCast] using he

end ThreeSum.DenseGuardWanted

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Summing the actual dense-guard branches in physical slot order

The counter at slot i is the mass of slots before i. The expensive branch
is charged only when adding the current mass still fits the threshold.
These charges sum to at most that threshold, including when a later slot
crosses it. No bound on the mass of the crossing slot is required.
-/

namespace ThreeSum.SharedTraversalCosts
open _root_.ThreeSum.SharedTraversalCosts


open _root_.Finset
open scoped _root_.BigOperators





theorem prefixMass_zero (mass : ℕ → ℕ) : _root_.ThreeSum.SharedTraversalCosts.prefixMass mass 0=0 := by simp [_root_.ThreeSum.SharedTraversalCosts.prefixMass]

theorem prefixMass_succ (mass : ℕ → ℕ) (n : ℕ) :
    _root_.ThreeSum.SharedTraversalCosts.prefixMass mass (n+1)=_root_.ThreeSum.SharedTraversalCosts.prefixMass mass n+mass n := by
  simp only [_root_.ThreeSum.SharedTraversalCosts.prefixMass,sum_range_succ]













end ThreeSum.SharedTraversalCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Original-value soundness and completeness on the bounded reporting domain -/

namespace ThreeSum.BandRawA
open _root_.ThreeSum.BandRawA


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.Finset

set_option maxHeartbeats 1200000
set_option maxRecDepth 7000



theorem finite_original_equation_complete {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {a b c : ℤ} (hg : 0 < g)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·))
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ha : a ∈ originalA) (hb : b ∈ originalB) (hc : c ∈ originalC) (heq : a+b=c) :
    ∃ t ∈ _root_.ThreeSum.BandRawA.finiteAllProducts A.length B.length C.length g (_root_.ThreeSum.BandRawA.sortedRecords A B C g hg hsA hsB hsC),
      _root_.ThreeSum.BandRawA.valueAt A.length g (_root_.ThreeSum.BandRawA.sortedRecords A B C g hg hsA hsB hsC)
        (fun i => A.getD i 0) t.1.val=a ∧ B.getD t.2.1.val 0=b ∧ C.getD t.2.2.val 0=c := by
  obtain ⟨t,ht,hvalues⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.original_equation_complete hg hsA hsB hsC hA hB hC ha hb hc heq
  obtain ⟨u,hu,he⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.finite_lift ht
  refine ⟨u,hu,?_⟩
  change _root_.ThreeSum.BandRawA.valueAt A.length g (_root_.ThreeSum.BandRawA.sortedRecords A B C g hg hsA hsB hsC)
    (fun i => A.getD i 0) (_root_.ThreeSum.BandRawA.coordinates u).1=a ∧
      B.getD (_root_.ThreeSum.BandRawA.coordinates u).2.1 0=b ∧ C.getD (_root_.ThreeSum.BandRawA.coordinates u).2.2 0=c
  rw [he]
  exact hvalues

theorem finite_original_equation_sound {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record}
    {t : Fin (_root_.ThreeSum.BandRawA.items A.length g rs).length × Fin B.length × Fin C.length}
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ht : t ∈ _root_.ThreeSum.BandRawA.finiteAllProducts A.length B.length C.length g rs)
    (heq : _root_.ThreeSum.BandRawA.valueAt A.length g rs (fun i => A.getD i 0) t.1.val+
      B.getD t.2.1.val 0=C.getD t.2.2.val 0) :
    ∃ a ∈ originalA, ∃ b ∈ originalB, ∃ c ∈ originalC, a+b=c :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.original_equation_sound hA hB hC (_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.mem_finiteAllProducts.mp ht) heq

end ThreeSum.BandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Owner queries are the exact fibers of the global physical domain

The A incidence fixes its owner. Restricting to that owner's B/C bands
therefore leaves the entire wanted fiber unchanged. The mass read by the
owner-local query is exactly the mass charged by the global dense guard.
-/

namespace ThreeSum.DenseGuardBands
open _root_.ThreeSum.DenseGuardBands


open _root_.Finset
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout

section General

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem domain_eq_of_first_fiber {h J : ℕ} {P shift : ℤ}
    (T U : Finset (_root_.ThreeSum.RawIncidences.Original α β γ)) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (hf : ∀ t : _root_.ThreeSum.RawIncidences.Original α β γ, t.1=w.1 → (t ∈ T ↔ t ∈ U)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P shift T a b c) w=_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P shift U a b c) w := by
  ext r
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain,mem_filter,_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.mem_rawOn]
  constructor
  · rintro ⟨⟨ht,hr⟩,he⟩
    have ha : r.1.1=w.1 := congrArg (fun z : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α => z.1) he
    exact ⟨⟨(hf r.1 ha).mp ht,hr⟩,he⟩
  · rintro ⟨⟨hu,hr⟩,he⟩
    have ha : r.1.1=w.1 := congrArg (fun z : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α => z.1) he
    exact ⟨⟨(hf r.1 ha).mpr hu,hr⟩,he⟩

end General

open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA

theorem finite_owner_fiber {nA nB nC g s : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record}
    (hs : s < rs.length) (i : Fin (_root_.ThreeSum.BandRawA.items nA g rs).length)
    (hi : (_root_.ThreeSum.BandRawA.labelAt nA g rs i.val).owner=s)
    (t : Fin (_root_.ThreeSum.BandRawA.items nA g rs).length × Fin nB × Fin nC) (ht : t.1=i) :
    t ∈ _root_.ThreeSum.BandRawA.finiteAllProducts nA nB nC g rs ↔ t ∈ _root_.ThreeSum.BandRawA.finiteOwnerProduct nA nB nC g rs s := by
  have ho : (_root_.ThreeSum.BandRawA.labelAt nA g rs t.1.val).owner=s := by rw [ht]; exact hi
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.mem_finiteAllProducts,_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.mem_finiteOwnerProduct,_root_.ThreeSum.BandRawA.mem_allProducts,_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.mem_ownerProduct hs,
    _root_.ThreeSum.BandRawA.coordinates,_root_.ThreeSum.BandRawA.ownerRecord,ho,true_and]

theorem domain_global_eq_owner {h J nA nB nC g s : ℕ} {P shift : ℤ}
    (rs : List _root_.ThreeSum.BandCandidateRows.Record) (hs : s < rs.length)
    (a : Fin (_root_.ThreeSum.BandRawA.items nA g rs).length→ℤ) (b : Fin nB→ℤ) (c : Fin nC→ℤ)
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (Fin (_root_.ThreeSum.BandRawA.items nA g rs).length))
    (ho : (_root_.ThreeSum.BandRawA.labelAt nA g rs w.1.val).owner=s) :
    _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P shift (_root_.ThreeSum.BandRawA.finiteAllProducts nA nB nC g rs) a b c) w=
      _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P shift (_root_.ThreeSum.BandRawA.finiteOwnerProduct nA nB nC g rs s) a b c) w :=
  _root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardBands.domain_eq_of_first_fiber _ _ a b c w (_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardBands.finite_owner_fiber hs w.1 ho)

theorem prefixQuery_global_eq_owner {h J nA nB nC g s k : ℕ} {P shift : ℤ}
    (rs : List _root_.ThreeSum.BandCandidateRows.Record) (hs : s < rs.length)
    (a : Fin (_root_.ThreeSum.BandRawA.items nA g rs).length→ℤ) (b : Fin nB→ℤ) (c : Fin nC→ℤ)
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (Fin (_root_.ThreeSum.BandRawA.items nA g rs).length))
    (ho : (_root_.ThreeSum.BandRawA.labelAt nA g rs w.1.val).owner=s)
    (pre : List (Finset (Fin (464*h)))) :
    _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P shift (_root_.ThreeSum.BandRawA.finiteAllProducts nA nB nC g rs) a b c) w k pre=
      _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P shift (_root_.ThreeSum.BandRawA.finiteOwnerProduct nA nB nC g rs s) a b c) w k pre := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery,_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardBands.domain_global_eq_owner rs hs a b c w ho]

theorem rootMass_global_eq_owner {h J nA nB nC g s : ℕ} {P shift : ℤ}
    (rs : List _root_.ThreeSum.BandCandidateRows.Record) (hs : s < rs.length)
    (a : Fin (_root_.ThreeSum.BandRawA.items nA g rs).length→ℤ) (b : Fin nB→ℤ) (c : Fin nC→ℤ)
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (Fin (_root_.ThreeSum.BandRawA.items nA g rs).length))
    (ho : (_root_.ThreeSum.BandRawA.labelAt nA g rs w.1.val).owner=s) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P shift (_root_.ThreeSum.BandRawA.finiteAllProducts nA nB nC g rs) a b c) w=
      _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P shift (_root_.ThreeSum.BandRawA.finiteOwnerProduct nA nB nC g rs s) a b c) w :=
  _root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardBands.prefixQuery_global_eq_owner rs hs a b c w ho []

end ThreeSum.DenseGuardBands

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual finite budgets of the retained common-prime stage -/

namespace ThreeSum.EncodedColorPrimeCosts
open _root_.ThreeSum.EncodedColorPrimeCosts


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds

















theorem moduli_pos {A B C : List ℤ} {g y : ℕ} {hg : 0 < g}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hy : 0 < y) (i : ℕ) : 0 < _root_.ThreeSum.LightEncodedColorPrime.moduli A B C g hg hsA hsB hsC y i :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeChoice.modulus_pos (_root_.ThreeSum.LightPrimePool.prime y)
    (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
    (_root_.ThreeSum.BandRawA.sortedRecords A B C g hg hsA hsB hsC) (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.size_pos hy)
    (fun j hj => (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_spec hj).1) i

theorem scheduled_modulus_eq (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    _root_.ThreeSum.LightEncodedColorPrime.moduli A B C (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC (_root_.ThreeSum.Scales.primeWindow n)
      (_root_.ThreeSum.LightBandPrimeDepth.depth (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.Scales.primeWindow n))=
      _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.modulus n A.length B.length C.length
        (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
        (_root_.ThreeSum.BandRawA.sortedRecords A B C (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC) := rfl

theorem scheduled_modulus_guard {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hR : 4 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :
    4*_root_.ThreeSum.LightEncodedColorPrime.moduli A B C (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC (_root_.ThreeSum.Scales.primeWindow n)
      (_root_.ThreeSum.LightBandPrimeDepth.depth (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.Scales.primeWindow n)) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts.scheduled_modulus_eq]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.modulus_guard _ _ _ _ hR

end ThreeSum.EncodedColorPrimeCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The actual wanted array on physical owner-incidence indices

The key constructor uses the mapped A-value list. The reporter and dense
owner domains use physical positions in the incidence-label list. Their
length-preserving transport keeps every physical position, lift and full
output record, including positions holding equal integer values.
-/

namespace ThreeSum.ReportingHostWantedPhysical
open _root_.ThreeSum.ReportingHostWantedPhysical


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding

set_option maxHeartbeats 2100000
set_option maxRecDepth 10000









theorem transport_injective {α β : Type*} {h J : ℕ} (e : α≃β) :
    Function.Injective (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.transport (h := h) (J := J) e) := by
  intro w w' he
  exact Prod.ext (e.injective (congrArg (fun z : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J β => z.1) he))
    (congrArg (fun z : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J β => z.2) he)

@[simp] theorem transport_symm {α β : Type*} {h J : ℕ} (e : α≃β)
    (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J β) : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.transport e (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.transport e.symm w)=w := by
  rcases w with ⟨i,q⟩
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.transport,Equiv.apply_symm_apply]

section Actual

variable {μ : ℕ→ℤ} {f : ℕ→ℤ} {n g free M P h J : ℕ}
  {rs : List _root_.ThreeSum.BandCandidateRows.Record} {shift : ℤ}
  (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output μ free M (_root_.ThreeSum.LightGuardedWanted.left P (_root_.ThreeSum.BandRawA.values f (_root_.ThreeSum.BandRawA.items n g rs)))
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right h J) (3*(_root_.ThreeSum.BandRawA.values f (_root_.ThreeSum.BandRawA.items n g rs)).length)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) shift)



theorem wantedAt_injective : Function.Injective (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt H) :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.transport_injective (_root_.ThreeSum.ReportingHostWantedPhysical.incidenceIndices f n g rs)).comp (_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardWanted.labelAt_injective H)

















/-- Every physical incidence/lift/output satisfying the key equation is an
actual emitted slot. This is the converse needed by the no-hit decision. -/
theorem wantedAt_complete (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (Fin (_root_.ThreeSum.BandRawA.items n g rs).length))
    (hk : (M : ℤ) ∣ _root_.ThreeSum.BandRawA.valueAt n g rs f w.1.val%(P : ℤ)+
      _root_.ThreeSum.RawIncidences.lift w.2.1*(P : ℤ)+shift-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2) :
    ∃ slot : Fin (μ free).toNat, _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt H slot=w := by
  let v := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.transport (_root_.ThreeSum.ReportingHostWantedPhysical.incidenceIndices f n g rs).symm w
  have hv : v∈_root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.wanted M P (_root_.ThreeSum.BandRawA.values f (_root_.ThreeSum.BandRawA.items n g rs)) h J shift :=
    _root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.mem_wanted.mpr hk
  obtain ⟨slot,hs⟩ := List.mem_ofFn.mp (_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardWanted.labels_complete H hv)
  refine ⟨slot,?_⟩
  change _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.transport (_root_.ThreeSum.ReportingHostWantedPhysical.incidenceIndices f n g rs) (_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardWanted.labelAt H slot)=w
  rw [hs]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.transport_symm _ w

end Actual

end ThreeSum.ReportingHostWantedPhysical

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Distinct original-position semantics of the finite owner catalog

Incidence coordinates remain physical coordinates in the flattened A row.
Original input indices are recovered from retained class membership. Their
different colors prove that the three recovered positions are distinct,
even when the input contains repeated values.
-/

namespace ThreeSum.BandRawA
open _root_.ThreeSum.BandRawA


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists

set_option maxHeartbeats 1500000
set_option maxRecDepth 8000







theorem finite_color_iff {n W g : ℕ} {A B C : List ℤ}
    (p : _root_.ThreeSum.Coloring.Parameter W) (x : Fin n → ℤ) (hg : 0 < g)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·))
    (hA : ∀ z, z ∈ A ↔ z ∈ _root_.ThreeSum.ColorClassLists.classList p x 0 1)
    (hB : ∀ z, z ∈ B ↔ z ∈ _root_.ThreeSum.ColorClassLists.classList p x 1 1)
    (hC : ∀ z, z ∈ C ↔ z ∈ _root_.ThreeSum.ColorClassLists.classList p x 2 (-1)) :
    _root_.ThreeSum.BandRawA.finiteEquation A B C g (_root_.ThreeSum.BandRawA.sortedRecords A B C g hg hsA hsB hsC) ↔ _root_.ThreeSum.ColorClassLists.witness p x := by
  constructor
  · rintro ⟨t,ht,heq⟩
    exact _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.finite_original_equation_sound hA hB hC ht heq
  · rintro ⟨a,ha,b,hb,c,hc,heq⟩
    obtain ⟨t,ht,hav,hbv,hcv⟩ :=
      _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.finite_original_equation_complete hg hsA hsB hsC hA hB hC ha hb hc heq
    refine ⟨t,ht,?_⟩
    rw [hav,hbv,hcv]
    exact heq



end ThreeSum.BandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # The same normalized finite witnesses and their actually selected prime -/

namespace ThreeSum.EncodedColorPrimeReadyData
open _root_.ThreeSum.EncodedColorPrimeReadyData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
open _root_.ThreeSum.EncodedColorLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData







theorem selected_pos {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)} :
    0 < _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC :=
  _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts.moduli_pos (lt_of_lt_of_le (by decide : 0 < 2) (_root_.ThreeSum.Scales.primeWindow_ge_two n)) _

theorem selected_guard {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hR : 4 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) : 4*_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n :=
  _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts.scheduled_modulus_guard hR

end ThreeSum.EncodedColorPrimeReadyData

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



theorem global_local_mass {h J n NB NC g p : ℕ} (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (_root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.globalItems h J n NB NC g p rs fA fB fC shift) w=
      _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.localItems h J n NB NC g p rs fA fB fC shift w) w :=
  _root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardBands.rootMass_global_eq_owner rs (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.owner_lt rs w) _ _ _ w rfl



theorem terminal_sound {h J n NB NC g p k : ℕ} (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (_root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs))
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.Terminal h J n NB NC g p rs fA fB fC shift w k) :
    ∃ t∈_root_.ThreeSum.BandRawA.finiteAllProducts n NB NC g rs,
      _root_.ThreeSum.RawIncidences.difference (fun i => _root_.ThreeSum.BandRawA.valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t=0 := by
  obtain ⟨pre,_,hhit⟩ := H
  obtain ⟨t,ht,ha,hzero⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalOriginal.hit_sound_original p shift
    (_root_.ThreeSum.BandRawA.finiteAIndices n g rs (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.owner rs w))
    (_root_.ThreeSum.BandRawA.finiteBandPositions NB g (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).b)
    (_root_.ThreeSum.BandRawA.finiteBandPositions NC g (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).c)
    (fun i => _root_.ThreeSum.BandRawA.valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.left rs fB w) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.right rs fC w)
    (_root_.ThreeSum.BandRawA.finiteBandEquiv NB g (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).b)
    (_root_.ThreeSum.BandRawA.finiteBandEquiv NC g (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).c)
    (fun _ => rfl) (fun _ => rfl) w pre (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.mem_owner rs w) hhit
  have hlocal : t∈_root_.ThreeSum.BandRawA.finiteOwnerProduct n NB NC g rs (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.owner rs w) := ht
  exact ⟨t,(_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardBands.finite_owner_fiber (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.owner_lt rs w) w.1 rfl t ha).mpr hlocal,hzero⟩

theorem terminal_of_raw {h J n NB NC g p k : ℕ} (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (_root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs)) (hk : k≤J)
    (r : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J (_root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs) (Fin NB) (Fin NC))
    (hr : r∈_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.globalItems h J n NB NC g p rs fA fB fC shift) (hw : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.wantedOf r=w)
    (hzero : _root_.ThreeSum.RawIncidences.difference (fun i => _root_.ThreeSum.BandRawA.valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) r.1=0) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.Terminal h J n NB NC g p rs fA fB fC shift w k := by
  have ha : r.1.1=w.1 := congrArg Prod.fst hw
  have hglobal := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.mem_rawOn.mp hr
  have hlocal : r.1∈_root_.ThreeSum.BandRawA.finiteOwnerProduct n NB NC g rs (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.owner rs w) :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardBands.finite_owner_fiber (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.owner_lt rs w) w.1 rfl r.1 ha).mp hglobal.1
  have hraw : r∈_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.localItems h J n NB NC g p rs fA fB fC shift w := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.mem_rawOn.mpr ⟨hlocal,hglobal.2⟩
  exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalOriginal.frontier_hit_of_raw p shift
    (_root_.ThreeSum.BandRawA.finiteAIndices n g rs (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.owner rs w))
    (_root_.ThreeSum.BandRawA.finiteBandPositions NB g (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).b)
    (_root_.ThreeSum.BandRawA.finiteBandPositions NC g (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).c)
    (fun i => _root_.ThreeSum.BandRawA.valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.left rs fB w) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.right rs fC w)
    (_root_.ThreeSum.BandRawA.finiteBandEquiv NB g (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).b)
    (_root_.ThreeSum.BandRawA.finiteBandEquiv NC g (_root_.ThreeSum.BandRawA.ownerRecord n g rs w.1.val).c)
    (fun _ => rfl) (fun _ => rfl) w hk r hraw hw hzero

section Actual

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n NB NC g free P h J : ℕ}
  {rs : List _root_.ThreeSum.BandCandidateRows.Record} {shift : ℤ}
  (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output μ free (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h^J)
    (_root_.ThreeSum.LightGuardedWanted.left P (_root_.ThreeSum.BandRawA.values fA (_root_.ThreeSum.BandRawA.items n g rs))) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right h J)
    (3*(_root_.ThreeSum.BandRawA.values fA (_root_.ThreeSum.BandRawA.items n g rs)).length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) shift)

theorem raw_emitted {r : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J (_root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs) (Fin NB) (Fin NC)}
    (hr : r∈_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.globalItems h J n NB NC g P rs fA fB fC shift) :
    ∃ slot : Fin (μ free).toNat, _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt H slot=_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.wantedOf r := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt_complete H
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.mem_witnesses.mp (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.mem_rawOn.mp hr).2).2
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus,Nat.cast_pow,_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.wantedOf,_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleKey] using hh

theorem original_zero_iff_emitted_terminal {k : ℕ}
    (hh : 0<h) (hp : 0<P) (hk : k≤J) :
    (∃ t∈_root_.ThreeSum.BandRawA.finiteAllProducts n NB NC g rs,
      _root_.ThreeSum.RawIncidences.difference (fun i => _root_.ThreeSum.BandRawA.valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t=0) ↔
      ∃ slot : Fin (μ free).toNat, _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.Terminal h J n NB NC g P rs fA fB fC shift (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt H slot) k := by
  constructor
  · rintro ⟨t,ht,hzero⟩
    obtain ⟨r,hr,hrt⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.raw_complete (h := h) (J := J) (P := (P : ℤ)) (d := shift)
      (a := fun i => _root_.ThreeSum.BandRawA.valueAt n g rs fA i.val) (b := fun j => fB j.val) (c := fun j => fC j.val)
      hh (by exact_mod_cast hp) ht (by rw [hzero]; exact dvd_zero _)
    obtain ⟨slot,hslot⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.raw_emitted H hr
    exact ⟨slot,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.terminal_of_raw rs fA fB fC shift (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt H slot) hk r hr hslot.symm
      (by simpa only [hrt] using hzero)⟩
  · rintro ⟨slot,hterminal⟩
    exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.terminal_sound rs fA fB fC shift (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt H slot) hterminal

end Actual

end ThreeSum.ReportingHostWantedOriginal

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The exact dense counter of the physical ascending wanted scan

The finite physical labels are injective even when input values repeat.
The sum of the queried owner masses in any prefix is consequently the
mass of a distinct-label prefix in the complete original domain.
-/

namespace ThreeSum.ReportingHostWantedPrefix
open _root_.ThreeSum.ReportingHostWantedPrefix


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
open _root_.ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum.SharedTraversalCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

section Actual

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n NB NC g free P h J : ℕ}
  {rs : List _root_.ThreeSum.BandCandidateRows.Record} {shift : ℤ}
  (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output μ free (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h^J)
    (_root_.ThreeSum.LightGuardedWanted.left P (_root_.ThreeSum.BandRawA.values fA (_root_.ThreeSum.BandRawA.items n g rs))) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right h J)
    (3*(_root_.ThreeSum.BandRawA.values fA (_root_.ThreeSum.BandRawA.items n g rs)).length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) shift)



theorem labels_nodup : (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.labels H).Nodup :=
  List.nodup_ofFn_ofInjective (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt_injective H)

theorem prefix_nodup (k : ℕ) : ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.labels H).take k).Nodup := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.labels_nodup H).take

theorem prefix_step (i : Fin (μ free).toNat) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.labels H).take (i.val+1)=(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.labels H).take i.val++[_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt H i] := by
  have hi : i.val<(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.labels H).length := by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.labels,List.length_ofFn] using i.isLt
  rw [List.take_succ_eq_append_getElem hi]
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.labels,List.getElem_ofFn]



theorem slotMass_at (fB fC : ℕ→ℤ) (NB NC : ℕ) (i : Fin (μ free).toNat) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.slotMass H fB fC NB NC i.val=
      _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.globalItems h J n NB NC g P rs fA fB fC shift) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt H i) := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.slotMass,dif_pos i.isLt]
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.global_local_mass rs fA fB fC shift (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt H i)).symm

theorem prefix_mass_eq (fB fC : ℕ→ℤ) (NB NC k : ℕ) (hk : k≤(μ free).toNat) :
    _root_.ThreeSum.SharedTraversalCosts.prefixMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.slotMass H fB fC NB NC) k=
      _root_.ThreeSum1960614.Machine.ThreeSum.DenseGuard.mass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.globalItems h J n NB NC g P rs fA fB fC shift) ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.labels H).take k) := by
  induction k with
  | zero => simp only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.prefixMass_zero,List.take_zero,_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuard.mass_nil]
  | succ k ih =>
      let i : Fin (μ free).toNat := ⟨k,by omega⟩
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.prefixMass_succ,ih (by omega)]
      rw [show (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.labels H).take (k+1)=(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.labels H).take k++[_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt H i] from _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.prefix_step H i]
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuard.mass_append,show _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.slotMass H fB fC NB NC k=
        _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.globalItems h J n NB NC g P rs fA fB fC shift) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt H i) from _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.slotMass_at H fB fC NB NC i]



theorem prefix_dense_yes (fB fC : ℕ→ℤ) (NB NC k F : ℕ) (aux : Finset ℤ)
    (hk : k≤(μ free).toNat) (hp : 0<P) (hg : 4*(P : ℤ)≤_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J)
    (hsep : ∀ t∈_root_.ThreeSum.BandRawA.finiteAllProducts n NB NC g rs,
      _root_.ThreeSum.RawIncidences.difference (fun i => _root_.ThreeSum.BandRawA.valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t≠0 →
        ∃ l∈aux, ¬l∣ _root_.ThreeSum.RawIncidences.difference (fun i => _root_.ThreeSum.BandRawA.valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t)
    (hF : _root_.ThreeSum.Arithmetic.weightedFalseCount (_root_.ThreeSum.BandRawA.finiteAllProducts n NB NC g rs)
      (_root_.ThreeSum.RawIncidences.difference (fun i => _root_.ThreeSum.BandRawA.valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)) aux (P : ℤ)≤F)
    (hdense : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J*F<_root_.ThreeSum.SharedTraversalCosts.prefixMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.slotMass H fB fC NB NC) k) :
    ∃ t∈_root_.ThreeSum.BandRawA.finiteAllProducts n NB NC g rs,
      _root_.ThreeSum.RawIncidences.difference (fun i => _root_.ThreeSum.BandRawA.valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t=0 := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.prefix_mass_eq H fB fC NB NC k hk] at hdense
  exact _root_.ThreeSum1960614.Machine.ThreeSum.DenseGuard.partial_early_yes_of_upper (_root_.ThreeSum.BandRawA.finiteAllProducts n NB NC g rs)
    (fun i => _root_.ThreeSum.BandRawA.valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)
    aux ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.labels H).take k) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.prefix_nodup H k) (by exact_mod_cast hp) hg hsep hF hdense

end Actual

end ThreeSum.ReportingHostWantedPrefix

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact whole-scan YES and NO for the original physical domain

Every emitted slot has its own original owner bands. Prefix threshold
crossings are sound by distinct physical labels; if no crossing occurs,
the terminal tests cover every original zero through an actual emitted slot.
-/

namespace ThreeSum.ReportingHostWantedDecision
open _root_.ThreeSum.ReportingHostWantedDecision


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
open _root_.ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix
open _root_.ThreeSum.LightReportingWantedScan
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScan
open _root_.ThreeSum.SharedTraversalCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts

set_option maxHeartbeats 2100000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

section Actual

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n NB NC g free P h J : ℕ}
  {rs : List _root_.ThreeSum.BandCandidateRows.Record} {shift : ℤ}
  (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output μ free (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h^J)
    (_root_.ThreeSum.LightGuardedWanted.left P (_root_.ThreeSum.BandRawA.values fA (_root_.ThreeSum.BandRawA.items n g rs))) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right h J)
    (3*(_root_.ThreeSum.BandRawA.values fA (_root_.ThreeSum.BandRawA.items n g rs)).length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) shift)



theorem slotHit_at (fB fC : ℕ→ℤ) (NB NC K : ℕ) (i : Fin (μ free).toNat) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedDecision.slotHit H fB fC NB NC K i.val ↔
      _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.Terminal h J n NB NC g P rs fA fB fC shift (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt H i) K := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedDecision.slotHit,dif_pos i.isLt]

theorem hit_exists_iff (fB fC : ℕ→ℤ) (NB NC K : ℕ) :
    (∃ i<(μ free).toNat, _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedDecision.slotHit H fB fC NB NC K i) ↔
      ∃ i : Fin (μ free).toNat, _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.Terminal h J n NB NC g P rs fA fB fC shift (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt H i) K := by
  constructor
  · rintro ⟨i,hi,hhit⟩
    exact ⟨⟨i,hi⟩,(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedDecision.slotHit_at H fB fC NB NC K ⟨i,hi⟩).mp hhit⟩
  · rintro ⟨i,hhit⟩
    exact ⟨i.val,i.isLt,(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedDecision.slotHit_at H fB fC NB NC K i).mpr hhit⟩

theorem accepted_iff_original (fB fC : ℕ→ℤ) (NB NC K F : ℕ) (aux : Finset ℤ)
    (hh : 0<h) (hK : K≤J) (hp : 0<P) (hg : 4*(P : ℤ)≤_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J)
    (hsep : ∀ t∈_root_.ThreeSum.BandRawA.finiteAllProducts n NB NC g rs,
      _root_.ThreeSum.RawIncidences.difference (fun i => _root_.ThreeSum.BandRawA.valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t≠0 →
        ∃ l∈aux, ¬l∣ _root_.ThreeSum.RawIncidences.difference (fun i => _root_.ThreeSum.BandRawA.valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t)
    (hF : _root_.ThreeSum.Arithmetic.weightedFalseCount (_root_.ThreeSum.BandRawA.finiteAllProducts n NB NC g rs)
      (_root_.ThreeSum.RawIncidences.difference (fun i => _root_.ThreeSum.BandRawA.valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)) aux (P : ℤ)≤F) :
    _root_.ThreeSum.LightReportingWantedScan.Accepted (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.slotMass H fB fC NB NC) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedDecision.slotHit H fB fC NB NC K)
      (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J*F) (μ free).toNat ↔
      ∃ t∈_root_.ThreeSum.BandRawA.finiteAllProducts n NB NC g rs,
        _root_.ThreeSum.RawIncidences.difference (fun i => _root_.ThreeSum.BandRawA.valueAt n g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val) t=0 := by
  constructor
  · rintro (hdense | hterminal)
    · exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.prefix_dense_yes H fB fC NB NC (μ free).toNat F aux le_rfl hp hg hsep hF hdense
    · exact (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.original_zero_iff_emitted_terminal H hh hp hK).mpr
        ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedDecision.hit_exists_iff H fB fC NB NC K).mp hterminal)
  · intro hzero
    exact Or.inr ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedDecision.hit_exists_iff H fB fC NB NC K).mpr
      ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.original_zero_iff_emitted_terminal H hh hp hK).mp hzero))



end Actual

end ThreeSum.ReportingHostWantedDecision

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Physical mass limits from the retained selected color

The positive common modulus, its guard, every physical incidence count,
and both original sorted-source lengths come from the executed pipeline.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData

set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}



theorem wanted_selected_guard (hR : 4≤_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :
    4*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)≤_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) := by
  have hh : 4*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)≤(_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n : ℤ) := by
    exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected_guard (A := A) (B := B) (C := C)
      (hsA := hsA) (hsB := hsB) (hsC := hsC) hR
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus,_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix,_root_.ThreeSum1960614.Machine.ThreeSum.Scales.localRadix,_root_.ThreeSum.SharedReportingBankResourceBounds.half,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks,Nat.cast_pow] using hh













end ThreeSum.SharedReportingBankResourceBounds

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













theorem original_zero_iff_witness {μ : ℕ→ℤ} {free n : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.OriginalZero n A B C hsA hsB hsC ↔ _root_.ThreeSum.ColorClassLists.witness color x := by
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.finite_color_iff color x (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC
    H.normalized.2.1.2.2.1 H.normalized.2.2.1.2.2.1 H.normalized.2.2.2.1.2.2.1]
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.OriginalZero _root_.ThreeSum.BandRawA.finiteEquation
  apply exists_congr
  intro t
  apply and_congr_right
  intro _
  dsimp only [_root_.ThreeSum.RawIncidences.difference]
  constructor <;> intro he <;> omega



end ThreeSum.ThreeSumWantedHostConditions

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostDecision

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum.ReportingHostWantedConsumerData
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions
open _root_.ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 15000
section

theorem ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostDecision.accepted_iff_witness__implementation_73ceea0065 {μ : ℕ→ℤ} {free n k : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.Ready k n) (hx : ∀ i, |x i|≤((n^k : ℕ) : ℤ)) :
    _root_.ThreeSum.LightReportingWantedScan.Accepted (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass H) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.hit H)
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.threshold n A B C hsA hsB hsC) (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC) ↔
        _root_.ThreeSum.ColorClassLists.witness color x := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedDecision.accepted_iff_original H.wanted
    (fun j => B.getD j 0) (fun j => C.getD j 0) B.length C.length
    (_root_.ThreeSum.LightSwitchDepth.depth (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC)
    (_root_.ThreeSum.DenseGuard.actualAux n) hn.half
    (by change 13*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)/20≤_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n); omega)
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected_pos (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_selected_guard hn.radix)
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.actual_separation H hn hx) (le_refl _)
  change _root_.ThreeSum.LightReportingWantedScan.Accepted (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass H) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.hit H)
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.threshold n A B C hsA hsB hsC)
      (μ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.wantedHeader free n
        (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length)).toNat ↔
        _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.OriginalZero n A B C hsA hsB hsC at hh
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count_read H,Int.toNat_natCast] at hh
  exact hh.trans (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.original_zero_iff_witness H)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostDecision.accepted_iff_witness__implementation_73ceea0065) := (@ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostDecision.accepted_iff_witness__implementation_73ceea0065)

#print axioms solution
