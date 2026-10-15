-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightThreeSumColor.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:12:24.450636+00:00
-- url     : https://prove2.me/submissions/3dc4abaf-f3b1-4ed4-9cc9-e2efef04d109

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorPipelineData_ordered
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorReportingData_report_le_source_allocation
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightEncodedColorReportingPipeline_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverMagnitude_rounds_bound
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingWantedScanStored_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightThreeSumWantedHost_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_Scales_scoreLoss_finite_bound
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_components
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_offset_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_threshold_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedTraversalCosts_prefix_time_le_dispatch_budget
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_ThreeSumColorBudgets_wanted_count_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_ThreeSumWantedHostCosts_physical_step_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_ThreeSumWantedHostDecision_accepted_iff_witness
import Theorems.Thm_ThreeSum_BandPrimeChoice_modulus_score_bound
import Theorems.Thm_ThreeSum_BandRawA_mem_aIndices_iff_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_allProducts
import Theorems.Thm_ThreeSum_BandRawA_mem_row
import Theorems.Thm_ThreeSum_BandRawA_owner_weightedFalseCount
import Theorems.Thm_ThreeSum_BandWeightedScore_block_bound
import Theorems.Thm_ThreeSum_LightPrimePool_prefix_increasing
import Theorems.Thm_ThreeSum_Scales_primeDepth_loss_bound

local instance platformRadixNonzero_2b12f7f687 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Filter
end Filter
namespace Finset
end Finset
namespace Light
end Light
namespace Real
end Real
namespace Set
end Set
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
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.BandWeightedScore
end ThreeSum.BandWeightedScore
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockSourceSharing
end ThreeSum.BlockSourceSharing
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.DenseGuardBands
end ThreeSum.DenseGuardBands
namespace ThreeSum.DenseGuardWanted
end ThreeSum.DenseGuardWanted
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.EncodedColorPrimeCosts
end ThreeSum.EncodedColorPrimeCosts
namespace ThreeSum.EncodedColorPrimeReadyData
end ThreeSum.EncodedColorPrimeReadyData
namespace ThreeSum.EncodedColorReportingData
end ThreeSum.EncodedColorReportingData
namespace ThreeSum.EncodedColorReportingResources
end ThreeSum.EncodedColorReportingResources
namespace ThreeSum.EncodedColorWantedConsumerData
end ThreeSum.EncodedColorWantedConsumerData
namespace ThreeSum.LightBandPrimeConstruction
end ThreeSum.LightBandPrimeConstruction
namespace ThreeSum.LightBandRawAResources
end ThreeSum.LightBandRawAResources
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightColorBands
end ThreeSum.LightColorBands
namespace ThreeSum.LightDenseSetup
end ThreeSum.LightDenseSetup
namespace ThreeSum.LightMinimum
end ThreeSum.LightMinimum
namespace ThreeSum.LightPrimePool
end ThreeSum.LightPrimePool
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightReportingWantedScanStored
end ThreeSum.LightReportingWantedScanStored
namespace ThreeSum.LightScales
end ThreeSum.LightScales
namespace ThreeSum.LightThreeSumColor
end ThreeSum.LightThreeSumColor
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.MassScales
end ThreeSum.MassScales
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostRelocation
end ThreeSum.ReportingHostRelocation
namespace ThreeSum.ReportingHostWantedConsumerData
end ThreeSum.ReportingHostWantedConsumerData
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum.ReportingHostWantedPhysical
end ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum.ReportingHostWantedPrefix
end ThreeSum.ReportingHostWantedPrefix
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
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts
namespace ThreeSum.SourceBandCosts
end ThreeSum.SourceBandCosts
namespace ThreeSum.SourceFiniteInputs
end ThreeSum.SourceFiniteInputs
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.ThreeSumColorBudgets
end ThreeSum.ThreeSumColorBudgets
namespace ThreeSum.ThreeSumFastResources
end ThreeSum.ThreeSumFastResources
namespace ThreeSum.ThreeSumFastResourcesColor
end ThreeSum.ThreeSumFastResourcesColor
namespace ThreeSum.ThreeSumReportingSetupData
end ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum.ThreeSumReportingSetupResources
end ThreeSum.ThreeSumReportingSetupResources
namespace ThreeSum.ThreeSumWantedHostCosts
end ThreeSum.ThreeSumWantedHostCosts
namespace ThreeSum.UniformStageBounds
end ThreeSum.UniformStageBounds
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
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
end ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
namespace ThreeSum1960614.Machine.ThreeSum.ColorClassLists
end ThreeSum1960614.Machine.ThreeSum.ColorClassLists
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
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
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources
end ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.HierarchyScales
end ThreeSum1960614.Machine.ThreeSum.HierarchyScales
namespace ThreeSum1960614.Machine.ThreeSum.LightBandPrimeConstruction
end ThreeSum1960614.Machine.ThreeSum.LightBandPrimeConstruction
namespace ThreeSum1960614.Machine.ThreeSum.LightBandRawAResources
end ThreeSum1960614.Machine.ThreeSum.LightBandRawAResources
namespace ThreeSum1960614.Machine.ThreeSum.LightClassFilter
end ThreeSum1960614.Machine.ThreeSum.LightClassFilter
namespace ThreeSum1960614.Machine.ThreeSum.LightColorBands
end ThreeSum1960614.Machine.ThreeSum.LightColorBands
namespace ThreeSum1960614.Machine.ThreeSum.LightDenseSetup
end ThreeSum1960614.Machine.ThreeSum.LightDenseSetup
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightMinimum
end ThreeSum1960614.Machine.ThreeSum.LightMinimum
namespace ThreeSum1960614.Machine.ThreeSum.LightPrimePool
end ThreeSum1960614.Machine.ThreeSum.LightPrimePool
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScanStored
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScanStored
namespace ThreeSum1960614.Machine.ThreeSum.LightScales
end ThreeSum1960614.Machine.ThreeSum.LightScales
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumColor
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumColor
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.MassScales
end ThreeSum1960614.Machine.ThreeSum.MassScales
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
end ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix
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
namespace ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
end ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandCosts
end ThreeSum1960614.Machine.ThreeSum.SourceBandCosts
namespace ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs
end ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.Switch
end ThreeSum1960614.Machine.ThreeSum.Switch
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets
end ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources
end ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor
end ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
end ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources
end ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions
end ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostCosts
end ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostCosts
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
end ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales
namespace ThreeSum1960614.Machine.ThreeSum.UniformStageBounds
end ThreeSum1960614.Machine.ThreeSum.UniformStageBounds
namespace ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder
end ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

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

theorem size_mono {n m g : ℕ} (h : n ≤ m) : _root_.ThreeSum.BandPartition.size n g ≤ _root_.ThreeSum.BandPartition.size m g := by
  by_cases hn : n = 0
  · simp [_root_.ThreeSum.BandPartition.size,hn]
  · have hm : m ≠ 0 := by omega
    have hd := Nat.div_le_div_right (c := g) (show n-1 ≤ m-1 by omega)
    simp only [_root_.ThreeSum.BandPartition.size,if_neg hn,if_neg hm]
    omega























end ThreeSum.BandPartition

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

































































section OriginalIndices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]









theorem mem_rawOn {h J : ℕ} {P d : ℤ} {T : Finset (_root_.ThreeSum.RawIncidences.Original α β γ)}
    {a : α → ℤ} {b : β → ℤ} {c : γ → ℤ} {r : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ} :
    r ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P d T a b c ↔
      r.1 ∈ T ∧ r.2 ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses h J P d (a r.1.1) (b r.1.2.1) (c r.1.2.2) :=
  Finset.mem_sigma





































end OriginalIndices

end ThreeSum.RawIncidences

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

















































theorem totalSize_upper (m : ℕ) : 1000000000 * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize m ≤ 203889696 * m := by
  have h := Nat.div_mul_le_self (203889696 * m) (20000000000 * _root_.ThreeSum.Scales.microSize m)
  convert h using 1 <;> simp only [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize, _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount] <;> ring



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
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Runs -/

/-- A procedure of a program is a procedure, with the same number, of the program with more
procedures appended. -/
theorem getElem?_append_of_eq_some {P : _root_.ThreeSum1960614.Machine.Light.Program} {p : ℕ} {body : _root_.ThreeSum1960614.Machine.Light.Stmt} (h : P[p]? = some body)
    (R : _root_.ThreeSum1960614.Machine.Light.Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h





/-- A run stays a run when procedures are appended to the program. -/
theorem Exec.append {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ σ' : _root_.ThreeSum1960614.Machine.Light.State} {c : ℕ} (h : _root_.ThreeSum1960614.Machine.Light.Exec lim P d s σ σ' c) (R : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Exec lim (P ++ R) d s σ σ' c := by
  induction h with
  | skip => exact _root_.ThreeSum1960614.Machine.Light.Exec.skip
  | set h => exact _root_.ThreeSum1960614.Machine.Light.Exec.set h
  | store h₁ h₂ h₃ => exact _root_.ThreeSum1960614.Machine.Light.Exec.store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.call h₁ (_root_.ThreeSum1960614.Machine.Light.getElem?_append_of_eq_some h₂ R) h₃ ih

/-! ## The rules -/





/-- What is proved about a program holds for the program with more procedures appended. -/
theorem Ends.append {s σ T Q} (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ T Q) (R : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim (P ++ R) d s σ T Q := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he.append R, hc, hq⟩























/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/


















/-! ## Simplification -/

attribute [simp] _root_.ThreeSum1960614.Machine.Light.Expr.val _root_.ThreeSum1960614.Machine.Light.Expr.cost _root_.ThreeSum1960614.Machine.Light.Expr.Safe _root_.Light.Op.eval _root_.ThreeSum1960614.Machine.Light.Cond.Holds _root_.ThreeSum1960614.Machine.Light.Cond.cost _root_.ThreeSum1960614.Machine.Light.Cond.Safe _root_.Light.frame







/-! ## The limits -/









end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The executable band size and its exact exponent

The band numerator is the integer ceiling of the square root of the actual
typed output count. The denominator is `2^floor(-bandShift*mu)`.
Euclidean division computes the rational exponent with bounded error.
-/

namespace ThreeSum.BandScales
open _root_.ThreeSum.BandScales


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open scoped _root_.Topology










theorem typedOutputs_pos (n : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs
  exact Nat.pow_pos (Nat.choose_pos (by omega))









noncomputable section























end

end ThreeSum.BandScales

end ThreeSum1960614.Machine

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

/-- From a theorem about a body to the specification. -/
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : _root_.ThreeSum1960614.Machine.Light.Stmt}
    (hp : P[p]? = some body)
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d body ⟨_root_.Light.frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩

/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩

/-- A specification holds with every larger bound on the time. -/
theorem Meets.mono_time (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T' := by omega) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R :=
  h.mono hT fun _ _ hR => hR



/-- A specification holds for the program with more procedures appended. -/
theorem Meets.append (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (P' : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim (P ++ P') p d vals μ T R := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, _root_.ThreeSum1960614.Machine.Light.getElem?_append_of_eq_some hp P', he.append P'⟩

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

























end ThreeSum.BandCandidateRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual finite hierarchy counts

These are the binomial counts used by the concrete microblock hierarchy.
Every prefix partition is included.  The integer switch and its rounding
allowance are applied before any asymptotic estimate is made.  The counts
in this module are combinatorial work counts; the implementation's operation
counts, raw wanted incidences, and false-mass bounds are separate interfaces.
-/

namespace ThreeSum.CostLedger
open _root_.ThreeSum.CostLedger


open _root_.Filter
open _root_.Set
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Switch
open scoped _root_.Topology
open scoped _root_.BigOperators

set_option maxHeartbeats 400000



















theorem bandCount_mul_bounds (n : ℕ) :
    n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n * _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n * _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n < n + _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n := by
  constructor
  · exact (ceilDiv_le_iff_le_mul (a := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (b := n)
      (c := _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n)).mp le_rfl
  · have h := Nat.div_mul_le_self (n + _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n - 1) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
    simp only [_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount, Nat.ceilDiv_eq_add_pred_div]
    rw [Nat.mul_comm (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)]
    have hpos := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n
    omega











noncomputable section















end
end ThreeSum.CostLedger

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









theorem prefix_nodup (y i : ℕ) : (_root_.ThreeSum.LightPrimePool.scanned y i).Nodup :=
  (_root_.ThreeSum.LightPrimePool.prefix_increasing y i).imp (fun h => Nat.ne_of_lt h)






theorem values_nodup (y : ℕ) : (_root_.ThreeSum.LightPrimePool.values y).Nodup := _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prefix_nodup y (3*y)






theorem size_eq_card (y : ℕ) : _root_.ThreeSum.LightPrimePool.size y = (_root_.ThreeSum.PrimeDensity.candidates y).card := by
  rw [← _root_.ThreeSum.LightPrimePool.values_toFinset,List.toFinset_card_of_nodup (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.values_nodup y)]
  rfl



theorem prime_spec {y i : ℕ} (hi : i < _root_.ThreeSum.LightPrimePool.size y) :
    Nat.Prime (_root_.ThreeSum.LightPrimePool.prime y i) ∧ y < _root_.ThreeSum.LightPrimePool.prime y i ∧ _root_.ThreeSum.LightPrimePool.prime y i ≤ 4*y :=
  _root_.ThreeSum.LightPrimePool.mem_values.mp (_root_.ThreeSum.LightPrimePool.prime_mem hi)

theorem prime_injective {y i j : ℕ} (hi : i < _root_.ThreeSum.LightPrimePool.size y) (hj : j < _root_.ThreeSum.LightPrimePool.size y)
    (heq : _root_.ThreeSum.LightPrimePool.prime y i = _root_.ThreeSum.LightPrimePool.prime y j) : i = j :=
  (List.getD_inj hi hj (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.values_nodup y)).mp heq



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
# Actual initialization of the integer block schedule

The fixed program computes all initial size parameters from the input
length. It uses the benchmark's proved logarithm, ceiling cube-root and
ceiling-half loops, with exact rounding bridges below. Division is used
only through an actual counting routine on the logarithmic numerator.
-/

namespace ThreeSum.LightScales
open _root_.ThreeSum.LightScales


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}



theorem root_le_self (m : ℕ) : Nat.nthRoot 3 m ≤ m :=
  (Nat.le_self_pow (by decide : 3 ≠ 0) (Nat.nthRoot 3 m)).trans
    (Nat.pow_nthRoot_le (Or.inl (by decide : 3 ≠ 0)))



theorem microHalf_le_self (m : ℕ) : _root_.ThreeSum.Scales.microHalf m ≤ m :=
  (Nat.div_le_self (Nat.nthRoot 3 m) 2).trans (_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.root_le_self m)

theorem blockCount_le (m : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount m ≤ 20*m := by
  by_cases hs : _root_.ThreeSum.Scales.microSize m=0
  · simp [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount,hs]
  · have hspos : 1 ≤ _root_.ThreeSum.Scales.microSize m := by omega
    have hJ : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount m ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount m*_root_.ThreeSum.Scales.microSize m := by
      calc
        _ = _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount m*1 := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ hspos
    have hu := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize_upper m
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize at hu
    omega

theorem totalSize_le_self (m : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize m ≤ m := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize_upper m
  omega























end ThreeSum.LightScales

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact relocation of closed verified procedure libraries

Every procedure call is shifted by the same list offset. The structural
execution proof preserves the exact initial/final states, runtime, memory
addresses, values, and depth budget. It permits composition of independently
verified fixed programs without assuming a new implementation contract.
-/

namespace ThreeSum.ReportingHostRelocation
open _root_.ThreeSum.ReportingHostRelocation


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light





theorem lookup {P : _root_.ThreeSum1960614.Machine.Light.Program} {p : ℕ} {body : _root_.ThreeSum1960614.Machine.Light.Stmt} (h : P[p]? = some body) (prefixProgram : _root_.ThreeSum1960614.Machine.Light.Program) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program prefixProgram P)[prefixProgram.length+p]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate prefixProgram.length body) := by
  apply _root_.ThreeSum1960614.Machine.Light.getElem?_append_length_add
  rw [List.getElem?_map,h]
  rfl

theorem exec {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ σ' : _root_.ThreeSum1960614.Machine.Light.State} {c : ℕ}
    (h : _root_.ThreeSum1960614.Machine.Light.Exec lim P d s σ σ' c) (prefixProgram : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Exec lim (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program prefixProgram P) d (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate prefixProgram.length s) σ σ' c := by
  induction h with
  | skip => exact _root_.ThreeSum1960614.Machine.Light.Exec.skip
  | set h => exact _root_.ThreeSum1960614.Machine.Light.Exec.set h
  | store h₁ h₂ h₃ => exact _root_.ThreeSum1960614.Machine.Light.Exec.store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.call h₁ (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.lookup h₂ prefixProgram) h₃ ih

theorem ends {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ : _root_.ThreeSum1960614.Machine.Light.State} {T : ℕ} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ T Q) (prefixProgram : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program prefixProgram P) d (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate prefixProgram.length s) σ T Q := by
  obtain ⟨σ',c,he,hc,hq⟩ := h
  exact ⟨σ',c,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.exec he prefixProgram,hc,hq⟩

theorem meets {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {p d : ℕ} {vals : List ℤ} {μ : ℕ → ℤ}
    {T : ℕ} {R : ℤ → (ℕ → ℤ) → Prop} (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (prefixProgram : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program prefixProgram P) (prefixProgram.length+p) d vals μ T R := by
  obtain ⟨body,hbody,he⟩ := h
  exact ⟨_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate prefixProgram.length body,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.lookup hbody prefixProgram,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.ends he prefixProgram⟩

end ThreeSum.ReportingHostRelocation

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















end ThreeSum.BandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The aggregate weighted score of physical band-owner candidates

Each flagged owner contributes the score of its three actual truncated
bands. Owner multiplicities are retained. The contraction and initial bound
therefore apply to the same quadratic catalog that the program scans.
-/

namespace ThreeSum.BandWeightedScore
open _root_.ThreeSum.BandWeightedScore


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000























theorem partialScore_bound (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (k : ℕ)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j) :
    _root_.ThreeSum.BandWeightedScore.partialScore primes s q nA nB nC g A B C rs k ≤ k*(s*g^3) := by
  calc
    _ ≤ ∑ _i ∈ range k, s*g^3 := sum_le_sum fun i _ => _root_.ThreeSum.BandWeightedScore.block_bound primes s q nA nB nC g A B C _ hprime hinj
    _ = _ := by simp

theorem score_bound (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j) :
    _root_.ThreeSum.BandWeightedScore.score primes s q nA nB nC g A B C rs ≤ rs.length*(s*g^3) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.partialScore_bound primes s q nA nB nC g A B C rs rs.length hprime hinj









end ThreeSum.BandWeightedScore

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





















theorem labelAt_mem {μ : ℕ → ℤ} {free M P h J : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output μ free M (_root_.ThreeSum.LightGuardedWanted.left P xs)
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right h J) (3*xs.length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) shift)
    (slot : Fin (μ free).toNat) : _root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardWanted.labelAt H slot ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.wanted M P xs h J shift := by
  obtain ⟨i,j,hi,_,hL,hR,hm⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordCoverage.output_pair H slot.isLt
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardWanted.labelAt,_root_.ThreeSum.DenseGuardWanted.leftIndex,_root_.ThreeSum.DenseGuardWanted.rightIndex,hL,hR,Int.toNat_natCast] using hm



end ThreeSum.DenseGuardWanted

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.ThreeSum.MassScales


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales
open scoped _root_.Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000























noncomputable section

































theorem false_mass_le {n k P H H1 : ℕ}
    (hscore : P * H ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.scoreLoss k n * H1)
    (hinit : H1 ≤ _root_.ThreeSum.Scales.candidateCount n * _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.rawTripleBound n)
    (hmod : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n ≤ _root_.ThreeSum.Scales.primeLoss _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n * P) :
    (H : ℝ) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseMajorant k n := by
  have hbound : H * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseNumerator k n := by
    calc
      H * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n ≤ _root_.ThreeSum.Scales.primeLoss _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n * (P * H) := by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using Nat.mul_le_mul_left H hmod
      _ ≤ _root_.ThreeSum.Scales.primeLoss _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n * (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.scoreLoss k n * H1) := Nat.mul_le_mul_left _ hscore
      _ ≤ _root_.ThreeSum.Scales.primeLoss _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n * (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.scoreLoss k n * (_root_.ThreeSum.Scales.candidateCount n * _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.rawTripleBound n)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hinit)
      _ = _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseNumerator k n := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseNumerator; ring
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseMajorant, le_div_iff₀ (show (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n by exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)]
  exact_mod_cast hbound

end
end ThreeSum.MassScales

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










theorem level_le {J k : ℕ} (hk : k ≤ _root_.ThreeSum.LightSwitchDepth.depth J) : k ≤ J := by
  have hh := Nat.div_mul_le_self (13*J) 20
  unfold _root_.ThreeSum.LightSwitchDepth.depth at hk
  omega

































end ThreeSum.SharedReportingBankLevels

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













theorem width_eq (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)*(464*_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) = 232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize _root_.ThreeSum.Scales.microSize _root_.ThreeSum.Scales.microHalf
  ring



















end ThreeSum.BlockSourceSharing

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

/-!
# A uniform size-only budget for the six principal stage counts

Both mass budgets are executable integer divisions of the concrete size
majorants.  The final bound is uniform in the input-dependent masses: the
eventual size threshold is chosen before `W`, `H`, `P`, or `H1` are quantified.
This remains a theorem about the specified finite work quantities, not a
claim that a complete machine has been proved to execute within them.
-/

namespace ThreeSum.UniformStageBounds
open _root_.ThreeSum.UniformStageBounds


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.Switch
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales
open _root_.ThreeSum.MassScales
open _root_.ThreeSum1960614.Machine.ThreeSum.MassScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open scoped _root_.Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000











noncomputable section

theorem false_le_budget {n k P H H1 : ℕ}
    (hscore : P * H ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.scoreLoss k n * H1)
    (hinit : H1 ≤ _root_.ThreeSum.Scales.candidateCount n * _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.rawTripleBound n)
    (hmod : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n ≤ _root_.ThreeSum.Scales.primeLoss _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n * P) : H ≤ _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.falseBudget k n := by
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.false_mass_le hscore hinit hmod
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseMajorant, le_div_iff₀ (show (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n by exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)] at hr
  apply (Nat.le_div_iff_mul_le (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)).mpr
  exact_mod_cast hr































end
end ThreeSum.UniformStageBounds

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

theorem ownerProduct_disjoint {nA nB nC g s t : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record}
    (hs : s < rs.length) (ht : t < rs.length) (hst : s ≠ t) :
    Disjoint (_root_.ThreeSum.BandRawA.ownerProduct nA nB nC g rs s) (_root_.ThreeSum.BandRawA.ownerProduct nA nB nC g rs t) := by
  apply disjoint_left.mpr
  intro x hx hy
  have hs' := (_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.mem_ownerProduct hs).mp hx
  have ht' := (_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.mem_ownerProduct ht).mp hy
  exact hst (hs'.2.1.symm.trans ht'.2.1)









theorem sum_allProducts (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List _root_.ThreeSum.BandCandidateRows.Record) :
    (∑ t ∈ _root_.ThreeSum.BandRawA.allProducts nA nB nC g rs, F t)=
      ∑ s ∈ range rs.length, ∑ t ∈ _root_.ThreeSum.BandRawA.ownerProduct nA nB nC g rs s, F t := by
  unfold _root_.ThreeSum.BandRawA.allProducts
  apply sum_biUnion
  intro s hs t ht hst
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.ownerProduct_disjoint (mem_range.mp hs) (mem_range.mp ht) hst



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

theorem modulus_score_bound {y nA nB nC g U : ℕ}
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (levels : ℕ) (hy : 1 < y)
    (hA : ∀ i < nA, |A i| ≤ (U : ℤ))
    (hB : ∀ i < nB, |B i| ≤ (U : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (U : ℤ)) :
    (_root_.ThreeSum.LightPrimePool.size y)^levels * _root_.ThreeSum.BandWeightedScore.score
      (_root_.ThreeSum.LightPrimePool.prime y) (_root_.ThreeSum.LightPrimePool.size y)
      (_root_.ThreeSum.LightBandPrimeConstruction.modulus y nA nB nC g A B C rs levels) nA nB nC g A B C rs ≤
      (Nat.log y (3*U))^levels * _root_.ThreeSum.BandWeightedScore.score
        (_root_.ThreeSum.LightPrimePool.prime y) (_root_.ThreeSum.LightPrimePool.size y) 1 nA nB nC g A B C rs :=
  _root_.ThreeSum.BandPrimeChoice.modulus_score_bound (_root_.ThreeSum.LightPrimePool.prime y) (_root_.ThreeSum.LightPrimePool.size y)
    nA nB nC g y U levels A B C rs hy (fun i hi => (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_spec hi).1)
    (fun i hi j hj heq => _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_injective hi hj heq)
    (fun i hi => (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_spec hi).2.1.le) hA hB hC













variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs y levels free maxMod U : ℕ}



end ThreeSum.LightBandPrimeConstruction

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Finite charge of the actual original-band histogram and bucket catalog -/

namespace ThreeSum.SourceBandCosts
open _root_.ThreeSum.SourceBandCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

theorem choose_mul_le (L K N M : ℕ) : L.choose K*N.choose M ≤ (L+N).choose (K+M) := by
  rw [Nat.add_choose_eq]
  exact Finset.single_le_sum (f := fun ij : ℕ×ℕ => L.choose ij.1*N.choose ij.2)
    (fun _ _ => Nat.zero_le _) (by simp : (K,M) ∈ Finset.HasAntidiagonal.antidiagonal (K+M))

theorem choose_pow_le (L K J : ℕ) : (L.choose K)^J ≤ (J*L).choose (J*K) := by
  induction J with
  | zero => simp
  | succ J ih =>
    calc
      _ = (L.choose K)^J*L.choose K := pow_succ _ _
      _ ≤ (J*L).choose (J*K)*L.choose K := Nat.mul_le_mul_right _ ih
      _ ≤ (J*L+L).choose (J*K+K) := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.choose_mul_le _ _ _ _
      _ = _ := by simp only [Nat.succ_mul]

theorem typedOutputs_le_fullOutputs (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.choose_pow_le (232*_root_.ThreeSum.Scales.muZero n) (_root_.ThreeSum.Scales.muZero n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))
  have hwidth : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)*(232*_root_.ThreeSum.Scales.muZero n)=232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu _root_.ThreeSum.Scales.muZero _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize
    ring
  have hcut : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)*_root_.ThreeSum.Scales.muZero n=_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := rfl
  rw [hwidth,hcut] at h
  exact h









theorem bandSize_le_fullOutputs (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n := by
  have hb : _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n := by
    apply (ceilDiv_le_iff_le_mul (a := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor_pos n)).mpr
    exact Nat.le_mul_of_pos_left _ (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor_pos n)
  have hr : _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n := by
    have hs := Nat.sqrt_le_self (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n-1)
    have hp := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.typedOutputs_pos n
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot _root_.ThreeSum.LocalCoverBounds.rootCeiling
    omega
  exact hb.trans (hr.trans (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.typedOutputs_le_fullOutputs n))











theorem size_le_bandCount {N n : ℕ} (hN : N ≤ n) : _root_.ThreeSum.BandPartition.size N (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n := by
  apply (_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono hN).trans
  by_cases hn : n=0
  · simp [hn,_root_.ThreeSum.BandPartition.size]
  · have hg := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n
    have hb := (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount_mul_bounds n).1
    have hb' : n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n := by simpa only [Nat.mul_comm] using hb
    have hd : (n-1)/_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n < _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n :=
      (Nat.div_lt_iff_lt_mul hg).mpr (by omega)
    simp only [_root_.ThreeSum.BandPartition.size,if_neg hn]
    omega





end ThreeSum.SourceBandCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The aggregate prime score is the exact physical incidence-product score

The executable A catalog supplies the first-coordinate values. Its owner
metadata supplies the B/C slices. Thus the mathematical score summed by
the actual prime selector counts this same domain with all multiplicities.
-/

namespace ThreeSum.BandRawA
open _root_.ThreeSum.BandRawA


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 1900000
set_option maxRecDepth 8000







theorem all_weightedFalseCount (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) :
    _root_.ThreeSum.Arithmetic.weightedFalseCount (_root_.ThreeSum.BandRawA.allProducts nA nB nC g rs)
      (_root_.ThreeSum.ModuloCounts.difference (_root_.ThreeSum.BandRawA.valueAt nA g rs A) B C)
      (_root_.ThreeSum.Auxiliary.moduli (_root_.ThreeSum.WeightedScore.auxiliarySet primes aux)) q=
      _root_.ThreeSum.BandWeightedScore.score primes aux q nA nB nC g A B C rs := by
  unfold _root_.ThreeSum.Arithmetic.weightedFalseCount
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.sum_allProducts]
  unfold _root_.ThreeSum.BandWeightedScore.score _root_.ThreeSum.BandWeightedScore.partialScore
  apply sum_congr rfl
  intro s hs
  exact _root_.ThreeSum.BandRawA.owner_weightedFalseCount primes aux q nA nB nC g A B C rs (mem_range.mp hs)













end ThreeSum.BandRawA

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

theorem modulus_loss (n nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n ≤ _root_.ThreeSum.Scales.primeLoss _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n*_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.modulus n nA nB nC A B C rs :=
  _root_.ThreeSum.Scales.primeDepth_loss_bound _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix (_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.modulus_bounds n nA nB nC A B C rs).1



theorem score_contraction {k n nA nB nC : ℕ} (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (hA : ∀ i < nA, |A i| ≤ (n^k : ℤ))
    (hB : ∀ i < nB, |B i| ≤ (n^k : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (n^k : ℤ)) :
    _root_.ThreeSum.Scales.candidateCount n^_root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n * _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.score n (_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.modulus n nA nB nC A B C rs) nA nB nC A B C rs ≤
      _root_.ThreeSum.Scales.divisorBudget k n^_root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n * _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.score n 1 nA nB nC A B C rs := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeConstruction.modulus_score_bound (y := _root_.ThreeSum.Scales.primeWindow n)
    (g := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (U := n^k) A B C rs (_root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n)
    (by have := _root_.ThreeSum.Scales.primeWindow_ge_two n; omega)
    (by simpa only [Nat.cast_pow] using hA)
    (by simpa only [Nat.cast_pow] using hB)
    (by simpa only [Nat.cast_pow] using hC)
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.size_eq_card,_root_.ThreeSum.Scales.candidateCount,_root_.ThreeSum.Scales.divisorBudget,_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.score,_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.modulus] using hh

theorem initial_score_bound {n nA nB nC : ℕ} (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (hcount : rs.length ≤ 3*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.score n 1 nA nB nC A B C rs ≤ _root_.ThreeSum.Scales.candidateCount n*_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.rawTripleBound n := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.score_bound (_root_.ThreeSum.LightPrimePool.prime (_root_.ThreeSum.Scales.primeWindow n))
    (_root_.ThreeSum.LightPrimePool.size (_root_.ThreeSum.Scales.primeWindow n)) 1 nA nB nC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) A B C rs
    (fun _ hi => (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_spec hi).1)
    (fun _ hi _ hj heq => _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_injective hi hj heq)
  calc
    _ ≤ rs.length*(_root_.ThreeSum.LightPrimePool.size (_root_.ThreeSum.Scales.primeWindow n)*_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n^3) := hh
    _ ≤ (3*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2)*(_root_.ThreeSum.LightPrimePool.size (_root_.ThreeSum.Scales.primeWindow n)*_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n^3) :=
      Nat.mul_le_mul_right _ hcount
    _ = _ := by rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.size_eq_card]; unfold _root_.ThreeSum.Scales.candidateCount _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.rawTripleBound; ring

theorem score_loss {k n nA nB nC : ℕ} (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (hbudget : _root_.ThreeSum.Scales.divisorBudget k n*_root_.ThreeSum.Scales.primeWindow n ≤
      _root_.ThreeSum.Scales.candidateCount n*(4*(k+2)*(_root_.ThreeSum.Scales.inputBits n+1)))
    (hA : ∀ i < nA, |A i| ≤ (n^k : ℤ))
    (hB : ∀ i < nB, |B i| ≤ (n^k : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (n^k : ℤ)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.modulus n nA nB nC A B C rs*_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.score n (_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.modulus n nA nB nC A B C rs) nA nB nC A B C rs ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.Scales.scoreLoss k n*_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.score n 1 nA nB nC A B C rs := by
  have hpos : 0 < (_root_.ThreeSum.PrimeDensity.candidates (_root_.ThreeSum.Scales.primeWindow n)).card := by
    rw [← _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.size_eq_card]
    exact _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.size_pos (by have := _root_.ThreeSum.Scales.primeWindow_ge_two n; omega)
  exact _root_.ThreeSum1960614.Machine.ThreeSum.Scales.scoreLoss_finite_bound hpos hbudget (_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.score_contraction A B C rs hA hB hC)
    (_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.modulus_bounds n nA nB nC A B C rs).2





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











theorem coordinates_injective {a b c : ℕ} :
    Function.Injective (@_root_.ThreeSum.BandRawA.coordinates a b c) := by
  rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ he
  simp only [_root_.ThreeSum.BandRawA.coordinates,Prod.mk.injEq] at he
  exact Prod.ext (Fin.ext he.1) (Prod.ext (Fin.ext he.2.1) (Fin.ext he.2.2))

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



theorem sum_finiteAllProducts (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List _root_.ThreeSum.BandCandidateRows.Record) :
    (∑ u ∈ _root_.ThreeSum.BandRawA.finiteAllProducts nA nB nC g rs, F (_root_.ThreeSum.BandRawA.coordinates u))=
      ∑ t ∈ _root_.ThreeSum.BandRawA.allProducts nA nB nC g rs, F t := by
  refine sum_bij (fun u _ => _root_.ThreeSum.BandRawA.coordinates u) ?_ ?_ ?_ ?_
  · intro u hu
    exact _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.mem_finiteAllProducts.mp hu
  · intro u hu v hv he
    exact _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.coordinates_injective he
  · intro t ht
    obtain ⟨u,hu,he⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.finite_lift ht
    exact ⟨u,hu,he⟩
  · intro u hu
    rfl



theorem finiteAll_weightedFalseCount (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) :
    _root_.ThreeSum.Arithmetic.weightedFalseCount (_root_.ThreeSum.BandRawA.finiteAllProducts nA nB nC g rs)
      (fun t => C t.2.2.val-B t.2.1.val-_root_.ThreeSum.BandRawA.valueAt nA g rs A t.1.val)
      (_root_.ThreeSum.Auxiliary.moduli (_root_.ThreeSum.WeightedScore.auxiliarySet primes aux)) q=
      _root_.ThreeSum.BandWeightedScore.score primes aux q nA nB nC g A B C rs := by
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.all_weightedFalseCount primes aux q nA nB nC g A B C rs]
  unfold _root_.ThreeSum.Arithmetic.weightedFalseCount
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.sum_finiteAllProducts
    (fun t => if (q : ℤ) ∣ _root_.ThreeSum.ModuloCounts.difference (_root_.ThreeSum.BandRawA.valueAt nA g rs A) B C t then
      _root_.ThreeSum.Arithmetic.missWeight (_root_.ThreeSum.Auxiliary.moduli (_root_.ThreeSum.WeightedScore.auxiliarySet primes aux))
        (_root_.ThreeSum.ModuloCounts.difference (_root_.ThreeSum.BandRawA.valueAt nA g rs A) B C t) else 0) nA nB nC g rs





end ThreeSum.BandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact resource formulas for the original-input band and incidence program

These formulas use the existing selected-color layout without changing any
address or procedure. The physical BC, AB, AC owner records and the packed
value, owner, and sorted-position arrays are all included in the extent.
-/

namespace ThreeSum.LightBandRawAResources
open _root_.ThreeSum.LightBandRawAResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.EncodedColorLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000









theorem count_le (n g : ℕ) : _root_.ThreeSum.ColorBandBounds.count n g ≤ 3*n^2 :=
  Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le n g) 2)







end ThreeSum.LightBandRawAResources

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

/-!
# Construct the dense-stop threshold from actual cover and source records

The host computes the representation cap, recomputes the exact aggregate
weighted score at the selected common modulus, multiplies the two, and
initializes the running counter. The four retained cells are counter,
threshold, representation cap and weighted score. Scratch starts after them.
-/

namespace ThreeSum.LightDenseSetup
open _root_.ThreeSum.LightDenseSetup


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

















theorem falseScore_eq (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) :
    _root_.ThreeSum.LightDenseSetup.falseScore primes s q nA nB nC g A B C rs=
      _root_.ThreeSum.BandWeightedScore.score primes s q nA nB nC g A B C rs :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.finiteAll_weightedFalseCount primes s q nA nB nC g A B C rs

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs q aux s cover free maxMod U h J : ℕ}



end ThreeSum.LightDenseSetup

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













section Actual

variable {μ : ℕ→ℤ} {f : ℕ→ℤ} {n g free M P h J : ℕ}
  {rs : List _root_.ThreeSum.BandCandidateRows.Record} {shift : ℤ}
  (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output μ free M (_root_.ThreeSum.LightGuardedWanted.left P (_root_.ThreeSum.BandRawA.values f (_root_.ThreeSum.BandRawA.items n g rs)))
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right h J) (3*(_root_.ThreeSum.BandRawA.values f (_root_.ThreeSum.BandRawA.items n g rs)).length)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) shift)













theorem wantedAt_key (slot : Fin (μ free).toNat) :
    (M : ℤ) ∣ _root_.ThreeSum.BandRawA.valueAt n g rs f (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt H slot).1.val%(P : ℤ)+
      _root_.ThreeSum.RawIncidences.lift (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt H slot).2.1*(P : ℤ)+shift-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt H slot).2.2 := by
  exact _root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.mem_wanted.mp (_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardWanted.labelAt_mem H slot)









end Actual

end ThreeSum.ReportingHostWantedPhysical

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







theorem count_mono {nA nB nC nA' nB' nC' g : ℕ} (ha : nA ≤ nA') (hb : nB ≤ nB') (hc : nC ≤ nC') :
    _root_.ThreeSum.LightEncodedColorPrime.count nA nB nC g ≤ _root_.ThreeSum.LightEncodedColorPrime.count nA' nB' nC' g := by
  have a := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono (g := g) ha
  have b := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono (g := g) hb
  have c := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono (g := g) hc
  unfold _root_.ThreeSum.LightEncodedColorPrime.count
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul b c) (Nat.mul_le_mul a b)) (Nat.mul_le_mul a c)









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





theorem global_local_mass {h J n NB NC g p : ℕ} (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J (_root_.ThreeSum.ReportingHostWantedOriginal.AType n g rs)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.globalItems h J n NB NC g p rs fA fB fC shift) w=
      _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.localItems h J n NB NC g p rs fA fB fC shift w) w :=
  _root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardBands.rootMass_global_eq_owner rs (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.owner_lt rs w) _ _ _ w rfl







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
# Explicit finite resource envelopes for the executed shared reporting bank

The envelopes below include the entire header and metadata slab, every
compact payload and construction scratch region, all prefix/local counts,
packed keys, switch intermediates, and both independent source lengths.
They are derived from the actual finite host contract.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum.SharedReportingBankHeader
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader
open _root_.ThreeSum.SharedReportingBankRows
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows

set_option maxHeartbeats 2800000
set_option maxRecDepth 14000
























theorem total_le {NB NC n h J g : ℕ} (hB : NB ≤ n) (hC : NC ≤ n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total h J NB NC g ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J*n*n :=
  Nat.mul_le_mul (Nat.mul_le_mul_left _ ((_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le NB g).trans hB))
    ((_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le NC g).trans hC)

theorem space_le {free h J NB NC g n : ℕ} (hB : NB ≤ n) (hC : NC ≤ n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.space free h J NB NC g ≤ free+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.extent h J n := by
  have hP := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.total_le (h := h) (J := J) (g := g) hB hC
  have ho := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.offset_le h J
  have hm := Nat.mul_le_mul_left (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total h J NB NC g) ho
  have hp := Nat.mul_le_mul_right (5*_root_.ThreeSum.SharedReportingBankHeader.levels J+_root_.ThreeSum.SharedReportingBankHeader.levels J*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.cellBound h J) hP
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.space
  apply max_le
  · unfold _root_.ThreeSum.SharedReportingBankHeader.records _root_.ThreeSum.LightPascal.tableSize _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.extent
    omega
  · unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rowBase _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.payload _root_.ThreeSum.SharedReportingBankHeader.records _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.extent
    nlinarith





end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retained normalized pointers and the actual incidence-count cell -/

namespace ThreeSum.EncodedColorNormalizedData
open _root_.ThreeSum.EncodedColorNormalizedData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum.EncodedColorLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout





theorem records_length_le {A B C : List ℤ} {g n : ℕ} {hg : 0 < g}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (ha : A.length ≤ n) (hb : B.length ≤ n) (hc : C.length ≤ n) :
    (_root_.ThreeSum.BandRawA.sortedRecords A B C g hg hsA hsB hsC).length ≤ _root_.ThreeSum.ColorBandBounds.count n g := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts.count_mono (g := g) ha hb hc
  have hright : _root_.ThreeSum.LightEncodedColorPrime.count n n n g=_root_.ThreeSum.ColorBandBounds.count n g := by
    unfold _root_.ThreeSum.LightEncodedColorPrime.count _root_.ThreeSum.ColorBandBounds.count
    ring
  rw [hright] at h
  simp only [_root_.ThreeSum.BandRawA.sortedRecords, _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.records_length]
  exact h







end ThreeSum.EncodedColorNormalizedData

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











theorem slotMass_at (fB fC : ℕ→ℤ) (NB NC : ℕ) (i : Fin (μ free).toNat) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.slotMass H fB fC NB NC i.val=
      _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.globalItems h J n NB NC g P rs fA fB fC shift) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt H i) := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.slotMass,dif_pos i.isLt]
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.global_local_mass rs fA fB fC shift (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt H i)).symm







end Actual

end ThreeSum.ReportingHostWantedPrefix

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












theorem primitive_bounds (n : ℕ) :
    _root_.ThreeSum.SharedReportingBankResourceBounds.half n ≤ _root_.ThreeSum.Scales.inputBits n ∧ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n ≤ 20*_root_.ThreeSum.Scales.inputBits n ∧
    2*_root_.ThreeSum.SharedReportingBankResourceBounds.half n*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n ≤ _root_.ThreeSum.Scales.inputBits n ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) ≤ 232*_root_.ThreeSum.Scales.inputBits n := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.microHalf_le_self (_root_.ThreeSum.Scales.inputBits n)
  have hj := _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.blockCount_le (_root_.ThreeSum.Scales.inputBits n)
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.totalSize_le_self (_root_.ThreeSum.Scales.inputBits n)
  change _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n*(2*_root_.ThreeSum.SharedReportingBankResourceBounds.half n) ≤ _root_.ThreeSum.Scales.inputBits n at ht
  refine ⟨hh,hj,by nlinarith,?_⟩
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth
  nlinarith







theorem band_le_magnitude (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n := by
  have hB := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.bandSize_le_fullOutputs n
  have hfull : _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n ≤ 2^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) := by
    rw [show _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)=232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n from _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.width_eq n]
    exact Nat.choose_le_two_pow _ _
  exact (hB.trans hfull).trans ((Nat.pow_le_pow_right (by decide) (by omega : width (half n) (blocks n) ≤
    width (half n) (blocks n)+1)).trans (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.components n).widthPower)













end ThreeSum.SharedReportingBankResourceBounds

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



theorem local_layer_le_magnitude (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n := by
  have hc : _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) ≤ 2^(464*_root_.ThreeSum.SharedReportingBankResourceBounds.half n) := Nat.choose_le_two_pow _ _
  exact hc.trans ((Nat.pow_le_pow_right (by decide) (by omega)).trans (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.components n).localPower)

theorem local_schedule_le_magnitude (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n := by
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.primitive_bounds n).1
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude.rounds_bound (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)).trans
    (Nat.pow_le_pow_right (by decide) (by omega))













end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Explicit finite scale bounds for reporter words and the dense counter -/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout

set_option maxHeartbeats 2800000
set_option maxRecDepth 14000







theorem wanted_modulus_le_magnitude (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)≤_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n := by
  have hp := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.components n).primePower
  exact (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero
    (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_prime (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)).ne_zero)).trans hp













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



theorem representation_cap_eq (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))=
      _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.representationBound n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.representationBound _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize_eq_length]

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

theorem records_length_le (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    (_root_.ThreeSum.BandRawA.sortedRecords A B C (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC).length ≤ 3*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2 := by
  obtain ⟨ha,hb,hc⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.normalized_lengths H
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.records_length_le ha hb hc
    (g := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (hg := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) (hsA := hsA) (hsB := hsB) (hsC := hsC)
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.size_le_bandCount (n := n) (le_refl n)
  exact hr.trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hs 2))







theorem false_score_eq (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC=
      _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.score n (_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.modulus n A.length B.length C.length
        (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
        (_root_.ThreeSum.BandRawA.sortedRecords A B C (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC))
        A.length B.length C.length (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
        (_root_.ThreeSum.BandRawA.sortedRecords A B C (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n) hsA hsB hsC) := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.falseScore
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetup.falseScore_eq]
  rfl

theorem false_score_le_budget {k : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hbudget : _root_.ThreeSum.Scales.divisorBudget k n*_root_.ThreeSum.Scales.primeWindow n ≤ _root_.ThreeSum.Scales.candidateCount n*(4*(k+2)*(_root_.ThreeSum.Scales.inputBits n+1)))
    (hx : ∀ i, |x i| ≤ ((n^k : ℕ) : ℤ)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC ≤ _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.falseBudget k n := by
  obtain ⟨ha,hb,hc⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.normalized_values H hx
  have ha' : ∀ j < A.length, |A.getD j 0| ≤ (n^k : ℤ) := by simpa only [Nat.cast_pow] using ha
  have hb' : ∀ j < B.length, |B.getD j 0| ≤ (n^k : ℤ) := by simpa only [Nat.cast_pow] using hb
  have hc' : ∀ j < C.length, |C.getD j 0| ≤ (n^k : ℤ) := by simpa only [Nat.cast_pow] using hc
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.false_score_eq]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.false_le_budget
    (_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.score_loss _ _ _ _ hbudget ha' hb' hc')
    (_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.initial_score_bound _ _ _ _ (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.records_length_le H))
    (_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeScales.modulus_loss n _ _ _ _ _ _ _)

theorem threshold_le_budget {k : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hbudget : _root_.ThreeSum.Scales.divisorBudget k n*_root_.ThreeSum.Scales.primeWindow n ≤ _root_.ThreeSum.Scales.candidateCount n*(4*(k+2)*(_root_.ThreeSum.Scales.inputBits n+1)))
    (hx : ∀ i, |x i| ≤ ((n^k : ℕ) : ℤ)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))*_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.falseBudget k n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.representationBound n := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.representation_cap_eq,Nat.mul_comm]
  exact Nat.mul_le_mul_right _ (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.false_score_le_budget H hbudget hx)

open _root_.Filter



end ThreeSum.ThreeSumColorBudgets

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

















noncomputable section













end
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

theorem prefix_le_report (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    free+8 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC := by
  obtain ⟨_,hf,hc,_,hs,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase
  omega





end ThreeSum.ThreeSumReportingSetupData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The original source header after shared reporting and dense initialization

The prefixProgram returns the source header unchanged. The reporting header starts
eight cells later, and its field six contains the initialized dense counter.
All contracts retain the same normalized A, B and C witnesses.
-/

namespace ThreeSum.EncodedColorReportingData
open _root_.ThreeSum.EncodedColorReportingData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000







theorem counter_read {μ : ℕ → ℤ} {free n : ℕ} {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)}
    {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC) :
    μ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC+14)=
      (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC : ℤ) := by
  have hh := H.catalog.heads 6 (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.header])
  simpa [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.header,_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase,_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.counter,Nat.add_assoc] using hh







end ThreeSum.EncodedColorReportingData

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













theorem record_count_le (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.recordCount n A B C hsA hsB hsC≤_root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) := by
  obtain ⟨ha,hb,hc⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.normalized_lengths H
  exact _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.records_length_le ha hb hc











end ThreeSum.EncodedColorWantedConsumerData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Charge the actual fixed153 wanted scan and fixed154 header caller

The concrete dispatcher contributes4500 operations, and the ascending
recursion contributes300 per slot. The exact active-branch mass remains
inside the cumulative guard until the original reporting ledger is applied.
-/

namespace ThreeSum.SharedTraversalCosts
open _root_.ThreeSum.SharedTraversalCosts


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000



variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]



/-- The time recurrence is the one proved for the actual153 executable. -/
theorem actual_scan_time_le {n k threshold count : ℕ} {mass stepTime : ℕ→ℕ}
    (hstep : ∀ i, stepTime i+300≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.slotEnvelope n threshold mass i)
    (hcount : count≤_root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.wantedBudget n)
    (hthreshold : threshold≤_root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.falseBudget k n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.representationBound n) :
    _root_.ThreeSum.LightReportingWantedScan.time stepTime count≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.dispatchBudget 4800 k n := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.prefix_time_le_dispatch_budget (mass := mass) (threshold := threshold)
    (by rfl) _ hcount hthreshold
  intro i
  rw [_root_.ThreeSum.LightReportingWantedScan.time]
  have hh := hstep i
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.slotEnvelope at hh
  omega





noncomputable section





end
end ThreeSum.SharedTraversalCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Relative limits for the complete wanted-header loader and scan

All numeric controls come from the input size. The loader starts its reusable
scratch at `counter+4`; every retained absolute pointer is handled by its
individual allocation end rather than being included in a numeric envelope.
-/

namespace ThreeSum.ThreeSumFastResources
open _root_.ThreeSum.ThreeSumFastResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds

set_option maxHeartbeats 2100000
set_option maxRecDepth 15000





theorem terminal_depth_le (n : ℕ) : _root_.ThreeSum.LightSwitchDepth.depth (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.level_le le_rfl

theorem record_cap_le (n : ℕ) : _root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^2 :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawAResources.count_le n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)).trans
    (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.input_le_magnitude n) 2))

theorem incidence_cap_le (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3 := by
  have hh := Nat.mul_le_mul (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.band_le_magnitude n) (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.record_cap_le n)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap
  calc
    _ ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n*(3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^2) := hh
    _ = _ := by ring

theorem radix_le (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n≤_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_modulus_le_magnitude n

theorem header_word_le (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.headerWord n≤_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n := by
  have hn := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.input_le_magnitude n
  have hJ := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.components n).blocksBound
  have hL := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.components n).localWidthBound
  have hK := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.terminal_depth_le n
  have hg := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.band_le_magnitude n
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.radix_le n
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.local_layer_le_magnitude n
  have hs : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)≤_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.local_schedule_le_magnitude n
  have hR := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.record_cap_le n
  have hN := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.incidence_cap_le n
  have h2 := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_power_le n 2 10 (by decide)
  have h3 := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_power_le n 3 10 (by decide)
  have hM : _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^10 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  have h1 : 1≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^10 := Nat.one_le_pow _ _ (by omega)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.headerWord _root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope
  omega

theorem header_slack_le (n : ℕ) : 50+2*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n≤_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n := by
  have hJ := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.components n).blocksBound
  have hM : _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^10 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  have h1 : 1≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^10 := Nat.one_le_pow _ _ (by omega)
  unfold _root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope
  omega

theorem scan_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {n U dst d : ℕ} (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.need n U).Ok lim dst d) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedScanNeed n U).Ok lim dst (d+1) :=
  hok.mono le_rfl le_rfl (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.need]; omega)



theorem header_space_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {n U counter d : ℕ}
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.need n U).Ok lim (counter+4) d) : counter+50+2*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n≤lim.space := by
  have hc := hok.cells
  change counter+4+_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n≤lim.space at hc
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.header_slack_le n
  omega

theorem header_word_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {n U dst d : ℕ}
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.need n U).Ok lim dst d) : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.headerWord n : ℤ)≤lim.word := by
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.header_word_le n).trans (Nat.le_mul_of_pos_right _ (by omega : 0<U+1))
  exact (Int.ofNat_le.mpr hh).trans hok.word

theorem outer_depth_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {n U dst d : ℕ}
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.need n U).Ok lim dst d) : d<lim.depth := by
  have hh := hok.depth
  change d+((_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).depth+_root_.ThreeSum.SharedReportingBankResourceBounds.wantedScanCount n+4+2)≤lim.depth at hh
  omega

noncomputable section



end
end ThreeSum.ThreeSumFastResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Compose the two actual reporting allocations at an arbitrary free pointer -/

namespace ThreeSum.ThreeSumReportingSetupResources
open _root_.ThreeSum.ThreeSumReportingSetupResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000



theorem counter_le {μ : ℕ → ℤ} {free n : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) (U : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC+
      (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.need n U).cells := by
  obtain ⟨_,hB,hC⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.normalized_lengths H
  exact (le_max_right _ _).trans (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.space_le
    (free := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC) (h := _root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n))
    (J := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (g := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) hB hC)





noncomputable section



end
end ThreeSum.ThreeSumReportingSetupResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Affine resources for source construction followed by reporting setup -/

namespace ThreeSum.EncodedColorReportingResources
open _root_.ThreeSum.EncodedColorReportingResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000







theorem counter_end_le_allocation {μ : ℕ → ℤ} {free n : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : 0 < n) (U : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC+4 ≤ free+(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.need n U).cells := by
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingData.report_le_source_allocation H hn U
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources.counter_le H U
  have hd : 4 ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.denseNeed n U).cells := by
    change 4 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.denseCells n U
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.denseCells
    omega
  dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.need,_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupResources.need]
  omega

noncomputable section



end
end ThreeSum.EncodedColorReportingResources

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

theorem kept_counter
    (K : _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).layoutHeader
      (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter 1) :
    _root_.ThreeSum1960614.Machine.Light.Kept μ ν (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter := by
  intro a ha
  have he : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).layoutHeader=
      (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter+4 := rfl
  exact K a ⟨by omega,Or.inl ha⟩











end ThreeSum.EncodedColorWantedConsumerData

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







theorem wanted_stored_threshold_le
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)*_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC≤
      9*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^8 := by
  have hrs : (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC).length≤3*n^2 :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.record_count_le H).trans
      (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) 2))
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_threshold_le (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC) hrs





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



















variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}













theorem label_key (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) ∣
      _root_.ThreeSum.BandRawA.valueAt A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC) (fun j => A.getD j 0) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.label H s).1.val %
        (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)+
      _root_.ThreeSum.RawIncidences.lift (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.label H s).2.1*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)+
      _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.shift n A B C hsA hsB hsC-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.label H s).2.2 := by
  have hm : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)=(_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n : ℤ) := by
    simp only [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus,_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix,_root_.ThreeSum1960614.Machine.ThreeSum.Scales.localRadix,Nat.cast_pow,_root_.ThreeSum.SharedReportingBankResourceBounds.half,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks]
  rw [hm]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt_key H.wanted (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.slot H s)

end ThreeSum.ReportingHostWantedConsumerData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # One affine allocation for a complete selected color

The prefixProgram retains its source and reporting catalogs, ending with the dense
counter. The wanted scan reuses scratch beginning four cells after that
counter. The two exact resource records are combined without bounding the
absolute starting address.
-/

namespace ThreeSum.ThreeSumFastResourcesColor
open _root_.ThreeSum.ThreeSumFastResourcesColor


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData

set_option maxHeartbeats 1800000
set_option maxRecDepth 15000



theorem prelude_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {free n U d : ℕ}
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.need n U).Ok lim free d) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.need n U).Ok lim free (d+1) :=
  H.mono (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.need]; omega) (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.need]; omega)
    (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.need]; omega)

theorem wanted_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {free ctr n U d : ℕ}
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.need n U).Ok lim free d)
    (hctr : ctr+4≤free+(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.need n U).cells) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.need n U).Ok lim (ctr+4) (d+1) :=
  H.mono (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.need]; omega) (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.need]; omega)
    (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.need]; omega)

theorem wanted_of_stored {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ→ℤ} {free n U d : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : 0<n) (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.need n U).Ok lim free d) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.need n U).Ok lim
      (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC+4) (d+1) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.wanted_of_ok hok (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingResources.counter_end_le_allocation H.encoded hn U)

theorem scan_of_stored {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ→ℤ} {free n U d : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : 0<n) (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.need n U).Ok lim free d) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedScanNeed n U).Ok lim
      (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC+4) (d+2) := by
  simpa only [Nat.add_assoc] using _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.scan_of_ok (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.wanted_of_stored H hn hok)



/-- The outer color call can load the counter at the returned source header plus14. -/
theorem counter_read_resources_of_stored {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ→ℤ} {free n U d : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : 0<n) (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.need n U).Ok lim free d) :
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC+15≤lim.space ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC+4≤lim.space := by
  have hw := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.wanted_of_stored H hn hok
  have hc := hw.cells
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.report_le_counter free n A B C hsA hsB hsC
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase at hp
  omega

theorem outer_depth_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {free n U d : ℕ}
    (H : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.need n U).Ok lim free d) : d<lim.depth := by
  have hd := H.depth
  dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.need] at hd
  omega

noncomputable section



end
end ThreeSum.ThreeSumFastResourcesColor

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Frozen physical order and the exact cost of the ascending consumer -/

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
open _root_.ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedTraversalCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts

set_option maxHeartbeats 2200000
set_option maxRecDepth 17000



variable {μ ν : ℕ→ℤ} {free n : ℕ}
  {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}









theorem mass_at (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass H s.val=_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.labelMass n A B C hsA hsB hsC (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.label H s) := by
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.slotMass_at H.wanted
    (fun j => B.getD j 0) (fun j => C.getD j 0) B.length C.length (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.slot H s)).trans
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.global_local_mass (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC)
        (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
        (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.shift n A B C hsA hsB hsC) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.label H s))



theorem stepTime_at (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.stepTime H s.val=
      _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatch.time (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC) (_root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n)
        (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.recordTime free n A B C hsA hsB hsC (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.label H s)
          (_root_.ThreeSum.ReportingHostWantedConsumerData.outputIndex μ (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC) s.val)
          (_root_.ThreeSum.SharedTraversalCosts.prefixMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass H) s.val) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.threshold n A B C hsA hsB hsC)) := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.stepTime,dif_pos s.isLt]







end ThreeSum.ReportingHostWantedConsumerData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # The actual154 wanted-header loader from its concrete Need

The executable loader and its exact scan call remain unchanged. Its
numeric controls and relative address bounds follow from the resource
record used by the complete selected-color program.
-/

namespace ThreeSum.ThreeSumFastResources
open _root_.ThreeSum.ThreeSumFastResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData

set_option maxHeartbeats 1900000
set_option maxRecDepth 17000

theorem header_word_eq (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.headerWord n=_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.word n := rfl

theorem program_meets {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d T U : ℕ} {μ : ℕ→ℤ} {free n params : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    {Q : ℤ→(ℕ→ℤ)→Prop}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (Hparams : _root_.ThreeSum1960614.Machine.Light.Seg μ params (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values n)) (hparams : params+19≤free)
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.need n U).Ok lim (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).layoutHeader d)
    (hscan : _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScan.program 152 (d+1)
      (_root_.ThreeSum.LightReportingWantedDispatch.arguments (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC)
        (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)) μ T Q) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.program 153 d
      [n,params,free,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC,
        _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC] μ (T+4000) Q := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.program_meets H Hparams hparams hok.space (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.outer_depth_of_ok hok)
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.header_space_of_ok hok) _ hscan
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.header_word_eq] using _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.header_word_of_ok hok

theorem color_program_meets {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d T U : ℕ} {μ : ℕ→ℤ} {free n params : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    {Q : ℤ→(ℕ→ℤ)→Prop}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (Hparams : _root_.ThreeSum1960614.Machine.Light.Seg μ params (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values n)) (hparams : params+19≤free)
    (hn : 0<n) (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.need n U).Ok lim free d)
    (hscan : _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScan.program 152 (d+2)
      (_root_.ThreeSum.LightReportingWantedDispatch.arguments (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC)
        (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)) μ T Q) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.program 153 (d+1)
      [n,params,free,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC,
        _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC] μ (T+4000) Q :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.program_meets H Hparams hparams (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.wanted_of_stored H hn hok) hscan

end ThreeSum.ThreeSumFastResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Execute the complete original physical wanted array

The invariant preserves the initial physical wanted order, all original
source data and all fixed dense metadata. The mutable counter is exactly
the mass of the ascending executed prefix until the first successful call.
-/

namespace ThreeSum.LightReportingWantedScanStored
open _root_.ThreeSum.LightReportingWantedScanStored


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
open _root_.ThreeSum.ReportingHostWantedConsumerData
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData
open _root_.ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedTraversalCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts

set_option maxHeartbeats 3200000
set_option maxRecDepth 22000
set_option linter.unusedSectionVars false



/-- At the actual schedule the selected modulus, complete prefix magnitudes
and dense threshold need no input-dependent numeric assumptions. -/
theorem program_meets_of_radix {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ→ℤ} {free n U d : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (hx : ∀ i, |x i|≤(U : ℤ)) (hR : 4≤_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n)
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedScanNeed n U).Ok lim (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).layoutHeader d) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScan.program 152 d
      (_root_.ThreeSum.LightReportingWantedDispatch.arguments (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC)
        (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)) μ (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.scanTime H.encoded)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ _root_.ThreeSum.LightReportingWantedScan.Accepted (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass H.encoded) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.hit H.encoded)
          (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.threshold n A B C hsA hsB hsC) (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)) ∧
        _root_.ThreeSum.LightReportingWantedScan.Counter (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass H.encoded) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.hit H.encoded)
          (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.threshold n A B C hsA hsB hsC) (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)
          (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter r ν ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).layoutHeader
          (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter 1) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScanStored.program_meets H hx _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected_pos (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_selected_guard hR)
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_stored_threshold_le H.encoded) hok

end ThreeSum.LightReportingWantedScanStored

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # The exact physical scan fits the uniform selected-color budget -/

namespace ThreeSum.ThreeSumWantedHostCosts
open _root_.ThreeSum.ThreeSumWantedHostCosts


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
open _root_.ThreeSum.ReportingHostWantedConsumerData
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData
open _root_.ThreeSum.SharedTraversalCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData

set_option maxHeartbeats 1800000
set_option maxRecDepth 15000

variable {μ : ℕ→ℤ} {free n k : ℕ}
  {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

theorem physical_steps_le
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) (i : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.stepTime H i+300≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.slotEnvelope n (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.threshold n A B C hsA hsB hsC) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass H) i := by
  by_cases hi : i<_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC
  · have hh := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostCosts.physical_step_le (free := free)
      (output := _root_.ThreeSum.ReportingHostWantedConsumerData.outputIndex μ (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC) i)
      (old := _root_.ThreeSum.SharedTraversalCosts.prefixMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass H) i) (threshold := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.threshold n A B C hsA hsB hsC)
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.label H ⟨i,hi⟩) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.label_key H ⟨i,hi⟩)
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.stepTime_at H ⟨i,hi⟩]
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.slotEnvelope
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass_at H ⟨i,hi⟩]
    exact hh
  · simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.stepTime,dif_neg hi]
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.slotEnvelope _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scalarOverhead
    omega

theorem physical_scan_time_le
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.Ready k n)
    (hx : ∀ i, |x i|≤((n^k : ℕ) : ℤ)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.scanTime H≤_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.dispatchBudget 4800 k n := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.actual_scan_time_le (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostCosts.physical_steps_le H)
  · have hh := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.wanted_count_le H
    rwa [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count_read H,Int.toNat_natCast] at hh
  · exact _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.threshold_le_budget H hn.divisor hx



end ThreeSum.ThreeSumWantedHostCosts

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColor

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
section

theorem ThreeSum1960614.Machine.ThreeSum.LightThreeSumColor.program_meets__implementation_95f392ad4e {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ→ℤ} {src n params row free k d : ℕ}
    (color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)) (x : Fin n→ℤ)
    (hn : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.Ready k n) (hsrc : src+n≤free) (hparams : params+19≤free) (hrow : row+6≤free)
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.need n (n^k)).Ok lim free d)
    (hread : _root_.ThreeSum1960614.Machine.Light.Seg μ src (List.ofFn x)) (hx : ∀ i, |x i|≤((n^k : ℕ) : ℤ))
    (hparameters : _root_.ThreeSum1960614.Machine.Light.Seg μ params (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values n))
    (hcolor : _root_.ThreeSum1960614.Machine.Light.Seg μ row (_root_.ThreeSum.ColorParameters.fields color)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColor.program 509 d [src,n,params,row,free] μ (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.colorBudget k n)
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ _root_.ThreeSum.ColorClassLists.witness color x) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ξ free) := by
  have hw := hok.space
  have hd := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.outer_depth_of_ok hok
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 509) (by rfl : program[509]?=some (body 354 508))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColor.body _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.colorBudget
  have hPrelude := ((_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorReportingPipeline.program_meets (d := d+1)
    color x hn.positive hn.radix hsrc hparams hrow
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.prelude_of_ok hok) hread hx hparameters hcolor).append
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumWantedHost.program.map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate 355))).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColor.body 354 508]
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorReportingPipeline.time] at hPrelude
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     first
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hPrelude _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hPrelude ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     on_goal -1 => (rintro header ν ⟨hout, hkeepPrelude⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  obtain ⟨A,hsA,B,hsB,C,hsC,hheader,H⟩ := hout
  let sourceHeader := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC
  let ctr := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC
  have hheader' : header=(sourceHeader : ℤ) := hheader
  have hctrRead : ν (sourceHeader+14)=(ctr : ℤ) := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingData.counter_read H
  obtain ⟨hsourceSpace,hctrSpace⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.counter_read_resources_of_stored
    H hn.positive hok
  change sourceHeader+15≤lim.space at hsourceSpace
  change ctr+4≤lim.space at hctrSpace
  have hsourceWord : (sourceHeader : ℤ)+14≤lim.word := by
    have hh := (Int.ofNat_le.mpr (show sourceHeader+14≤lim.space by omega)).trans hw
    exact_mod_cast hh
  have hctrWord : (ctr : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (show ctr≤lim.space by omega)).trans hw
  have hsourceNat : ((sourceHeader : ℤ)+14).toNat=sourceHeader+14 := by omega
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (ctr : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hheader', hctrRead, hsourceNat]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hheader', hctrRead, hsourceNat] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hheader', hctrRead, hsourceNat] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have paramsν : _root_.ThreeSum1960614.Machine.Light.Seg ν params (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values n) :=
    hparameters.of_kept hkeepPrelude (by change params+19≤free; exact hparams)
  have hScan := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScanStored.program_meets_of_radix H hx hn.radix
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesColor.scan_of_stored H hn.positive hok)
  have hWanted := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResources.color_program_meets H paramsν hparams hn.positive hok hScan
  have hWantedTime := hWanted.mono_time
    (Nat.add_le_add_right (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostCosts.physical_scan_time_le H.encoded hn hx) 4000)
  have hWantedCall := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.meets hWantedTime
    _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorReportingPipeline.program).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumColor.body 354 508]
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     first
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hWantedCall _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hWantedCall ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hheader', sourceHeader, ctr]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hheader', sourceHeader, ctr] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hheader', sourceHeader, ctr] <;> omega)
     on_goal -1 => (rintro result ξ ⟨hbool, hresult, _, hkeepScan⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hwitness := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostDecision.accepted_iff_witness H.encoded hn hx
  have hkept := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.kept_counter hkeepScan
  have hp := (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.prefix_le_report free n A B C hsA hsB hsC).1
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.report_le_counter free n A B C hsA hsB hsC
  exact ⟨hbool,hresult.trans hwitness,fun a ha =>
    (hkept a (by change a<_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.counter free n A B C hsA hsB hsC; omega)).trans (hkeepPrelude a ha)⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightThreeSumColor.program_meets__implementation_95f392ad4e) := (@ThreeSum1960614.Machine.ThreeSum.LightThreeSumColor.program_meets__implementation_95f392ad4e)

#print axioms solution
