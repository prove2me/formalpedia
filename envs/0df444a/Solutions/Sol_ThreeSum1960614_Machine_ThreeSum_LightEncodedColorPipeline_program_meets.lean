-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:06:19.486073+00:00
-- url     : https://prove2.me/submissions/40851c2d-ac1a-4dda-b41d-d4f0c8829e4f

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorParameterData_reads
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorPipelineData_ordered
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorPrimeData_Stored_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightCoverKeyData_Stored_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightEncodedColorPrimeHost_program_meets_input
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightEncodedColorResult_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightEncodedColorWantedHeader_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightEncodedColorWantedSources_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SourceBandBankData_Stored_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SourceBandBanksCosts_span_count_le_encoderCount
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SourceBandPairData_Stored_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SourceFiniteData_Normalized_keep
import Theorems.Thm_ThreeSum_BandRawA_mem_row
import Theorems.Thm_ThreeSum_Histograms_correlation_histograms
import Theorems.Thm_ThreeSum_LightMinimum_least_value_le
import Theorems.Thm_ThreeSum_LocalCoverBounds_pow_le_choose_mul

local instance platformRadixNonzero_35a089b5d3 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
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
namespace ThreeSum.Balancing
end ThreeSum.Balancing
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
namespace ThreeSum.BlockSourceCatalogCosts
end ThreeSum.BlockSourceCatalogCosts
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.BlockSourceSharing
end ThreeSum.BlockSourceSharing
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.EncodedColorPrimeCosts
end ThreeSum.EncodedColorPrimeCosts
namespace ThreeSum.EncodedColorPrimeData
end ThreeSum.EncodedColorPrimeData
namespace ThreeSum.EncodedColorPrimeReadyData
end ThreeSum.EncodedColorPrimeReadyData
namespace ThreeSum.EncodedColorStageCosts
end ThreeSum.EncodedColorStageCosts
namespace ThreeSum.EncodedColorWantedCosts
end ThreeSum.EncodedColorWantedCosts
namespace ThreeSum.EncodedColorWantedData
end ThreeSum.EncodedColorWantedData
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.GlobalKeyOffset
end ThreeSum.GlobalKeyOffset
namespace ThreeSum.Histograms
end ThreeSum.Histograms
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightBalancedOffset
end ThreeSum.LightBalancedOffset
namespace ThreeSum.LightBalancedWanted
end ThreeSum.LightBalancedWanted
namespace ThreeSum.LightBandPrimeConstruction
end ThreeSum.LightBandPrimeConstruction
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightColorBands
end ThreeSum.LightColorBands
namespace ThreeSum.LightCoverKeyData
end ThreeSum.LightCoverKeyData
namespace ThreeSum.LightEncodedColorPipeline
end ThreeSum.LightEncodedColorPipeline
namespace ThreeSum.LightGuardedWanted
end ThreeSum.LightGuardedWanted
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba
namespace ThreeSum.LightMinimum
end ThreeSum.LightMinimum
namespace ThreeSum.LightOriginalOffset
end ThreeSum.LightOriginalOffset
namespace ThreeSum.LightPrimePool
end ThreeSum.LightPrimePool
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSourceBucketBuild
end ThreeSum.LightSourceBucketBuild
namespace ThreeSum.LightSourceBucketSetup
end ThreeSum.LightSourceBucketSetup
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LightWantedJoin
end ThreeSum.LightWantedJoin
namespace ThreeSum.LightWantedSetup
end ThreeSum.LightWantedSetup
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum.RawAKeyLists
end ThreeSum.RawAKeyLists
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostRelocation
end ThreeSum.ReportingHostRelocation
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SourceBandBanksCosts
end ThreeSum.SourceBandBanksCosts
namespace ThreeSum.SourceBandCosts
end ThreeSum.SourceBandCosts
namespace ThreeSum.SourceBandHostCosts
end ThreeSum.SourceBandHostCosts
namespace ThreeSum.SourceBandLayout
end ThreeSum.SourceBandLayout
namespace ThreeSum.SourceBandPairCosts
end ThreeSum.SourceBandPairCosts
namespace ThreeSum.SourceBandPairData
end ThreeSum.SourceBandPairData
namespace ThreeSum.SourceBandPairSlices
end ThreeSum.SourceBandPairSlices
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.SourceControlCosts
end ThreeSum.SourceControlCosts
namespace ThreeSum.SourceFiniteCosts
end ThreeSum.SourceFiniteCosts
namespace ThreeSum.SourceFiniteData
end ThreeSum.SourceFiniteData
namespace ThreeSum.SourceFiniteInputs
end ThreeSum.SourceFiniteInputs
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales
namespace ThreeSum.WantedPairs
end ThreeSum.WantedPairs
namespace ThreeSum.WantedResidueKeys
end ThreeSum.WantedResidueKeys
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
end ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
namespace ThreeSum1960614.Machine.ThreeSum.Balancing
end ThreeSum1960614.Machine.ThreeSum.Balancing
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
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts
end ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
end ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
namespace ThreeSum1960614.Machine.ThreeSum.ColorClassLists
end ThreeSum1960614.Machine.ThreeSum.ColorClassLists
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.CyclicFold
end ThreeSum1960614.Machine.ThreeSum.CyclicFold
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
end ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts
end ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts
end ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts
end ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedData
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyOffset
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyOffset
namespace ThreeSum1960614.Machine.ThreeSum.Histograms
end ThreeSum1960614.Machine.ThreeSum.Histograms
namespace ThreeSum1960614.Machine.ThreeSum.Karatsuba
end ThreeSum1960614.Machine.ThreeSum.Karatsuba
namespace ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
end ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
namespace ThreeSum1960614.Machine.ThreeSum.LightBalancedOffset
end ThreeSum1960614.Machine.ThreeSum.LightBalancedOffset
namespace ThreeSum1960614.Machine.ThreeSum.LightBalancedWanted
end ThreeSum1960614.Machine.ThreeSum.LightBalancedWanted
namespace ThreeSum1960614.Machine.ThreeSum.LightBandPrimeConstruction
end ThreeSum1960614.Machine.ThreeSum.LightBandPrimeConstruction
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightClassFilter
end ThreeSum1960614.Machine.ThreeSum.LightClassFilter
namespace ThreeSum1960614.Machine.ThreeSum.LightColorBands
end ThreeSum1960614.Machine.ThreeSum.LightColorBands
namespace ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData
end ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData
namespace ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline
end ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline
namespace ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted
end ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
end ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
namespace ThreeSum1960614.Machine.ThreeSum.LightMinimum
end ThreeSum1960614.Machine.ThreeSum.LightMinimum
namespace ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset
end ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset
namespace ThreeSum1960614.Machine.ThreeSum.LightPrimePool
end ThreeSum1960614.Machine.ThreeSum.LightPrimePool
namespace ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
end ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBucketBuild
end ThreeSum1960614.Machine.ThreeSum.LightSourceBucketBuild
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSetup
end ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSetup
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightWantedJoin
end ThreeSum1960614.Machine.ThreeSum.LightWantedJoin
namespace ThreeSum1960614.Machine.ThreeSum.LightWantedSetup
end ThreeSum1960614.Machine.ThreeSum.LightWantedSetup
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
end ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
namespace ThreeSum1960614.Machine.ThreeSum.RawAKeyLists
end ThreeSum1960614.Machine.ThreeSum.RawAKeyLists
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
end ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts
end ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandCosts
end ThreeSum1960614.Machine.ThreeSum.SourceBandCosts
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandHostCosts
end ThreeSum1960614.Machine.ThreeSum.SourceBandHostCosts
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
end ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandPairCosts
end ThreeSum1960614.Machine.ThreeSum.SourceBandPairCosts
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandPairData
end ThreeSum1960614.Machine.ThreeSum.SourceBandPairData
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices
end ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.ThreeSum.SourceControlCosts
end ThreeSum1960614.Machine.ThreeSum.SourceControlCosts
namespace ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts
end ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts
namespace ThreeSum1960614.Machine.ThreeSum.SourceFiniteData
end ThreeSum1960614.Machine.ThreeSum.SourceFiniteData
namespace ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs
end ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.Switch
end ThreeSum1960614.Machine.ThreeSum.Switch
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales
namespace ThreeSum1960614.Machine.ThreeSum.WantedPairs
end ThreeSum1960614.Machine.ThreeSum.WantedPairs
namespace ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys
end ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

namespace ThreeSum1960614.Machine

/-! # An exact global offset chosen by a cyclic correlation -/

namespace ThreeSum.Balancing
open _root_.ThreeSum.Balancing


open _root_.Finset
open scoped _root_.BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]



theorem sum_correlation (F H : G → ℕ) :
    (∑ d, _root_.ThreeSum.Balancing.correlation F H d) = (∑ k, F k) * (∑ k, H k) := by
  unfold _root_.ThreeSum.Balancing.correlation
  rw [sum_comm]
  simp only [← mul_sum]
  have hshift (k : G) : (∑ d, H (k - d)) = ∑ d, H d := by
    exact Equiv.sum_comp (Equiv.subLeft k) H
  simp_rw [hshift]
  exact (sum_mul ..).symm

/-- The mean is exact for every table, with no hash-uniformity assumption. -/
theorem exists_balanced_offset (F H : G → ℕ) :
    ∃ d, Fintype.card G * _root_.ThreeSum.Balancing.correlation F H d ≤ (∑ k, F k) * (∑ k, H k) := by
  by_contra! h
  have hs : (∑ _d : G, (∑ k, F k) * (∑ k, H k)) <
      ∑ d, Fintype.card G * _root_.ThreeSum.Balancing.correlation F H d := by
    exact sum_lt_sum_of_nonempty (by simp) (by simpa using h)
  simp only [sum_const, nsmul_eq_mul, card_univ, ← mul_sum, _root_.ThreeSum1960614.Machine.ThreeSum.Balancing.sum_correlation] at hs
  exact (lt_irrefl _ hs)







end ThreeSum.Balancing

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








theorem size_mono {n m g : ℕ} (h : n ≤ m) : _root_.ThreeSum.BandPartition.size n g ≤ _root_.ThreeSum.BandPartition.size m g := by
  by_cases hn : n = 0
  · simp [_root_.ThreeSum.BandPartition.size,hn]
  · have hm : m ≠ 0 := by omega
    have hd := Nat.div_le_div_right (c := g) (show n-1 ≤ m-1 by omega)
    simp only [_root_.ThreeSum.BandPartition.size,if_neg hn,if_neg hm]
    omega

/-- A finite ceiling bound, including the empty input. -/
theorem size_mul_le (n g : ℕ) : _root_.ThreeSum.BandPartition.size n g*g ≤ n+g := by
  by_cases hn : n = 0
  · simp [_root_.ThreeSum.BandPartition.size,hn]
  · have hd := Nat.div_mul_le_self (n-1) g
    simp only [_root_.ThreeSum.BandPartition.size,if_neg hn,Nat.add_mul,Nat.one_mul]
    omega









theorem length_le (n g i : ℕ) : _root_.ThreeSum.BandPartition.stop n g i-_root_.ThreeSum.BandPartition.start g i ≤ g := by
  have hle : _root_.ThreeSum.BandPartition.stop n g i ≤ (i+1)*g := min_le_right _ _
  unfold _root_.ThreeSum.BandPartition.start
  simp only [Nat.add_mul,Nat.one_mul] at hle
  omega











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

























/-! ## A deterministic selected prime -/































/-! ## Exact integer rounding of the separable bucket cap -/













/-! ## The actual local parameters at `L=464*h` -/



































end ThreeSum.LocalCoverBounds

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
# Exact histogram and correlation counts

All weights are natural multiplicities.  In particular, raw A incidences and
repeated selected-map occurrences need not be deduplicated to use these
identities. The common offset is chosen from the actual key histograms.
-/

namespace ThreeSum.Histograms
open _root_.ThreeSum.Histograms


open _root_.Finset
open scoped _root_.BigOperators

variable {ι τ ν G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]



theorem sum_histogram (I : Finset ι) (key : ι → G) (weight : ι → ℕ) :
    (∑ k, _root_.ThreeSum.Histograms.histogram I key weight k) = ∑ i ∈ I, weight i := by
  unfold _root_.ThreeSum.Histograms.histogram
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  simp













end ThreeSum.Histograms

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

/-!
# Literal global-output records behind the radix key array

Local records use the verified layer enumerator's order and retain every
schedule occurrence. Cartesian extension enumerates each original global
output once. Mapping to integers may introduce equal values; the key array
retains all of those separate incidences.
-/

namespace ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.GlobalKeyEnumeration


open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.RadixKeyLists
open _root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
open scoped _root_.BigOperators

set_option maxHeartbeats 1800000









































theorem globalKeys_length (h J : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalKeys h J).length=_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h^J*_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h^J := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalKeys_eq_map,List.length_map,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords_length]







end ThreeSum.GlobalKeyEnumeration

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
# Costed signed residue conversion

This loop uses the benchmark's proved division-free remainder procedure.
Its sign argument supports either an ordinary histogram or a histogram of
the negated original integers. All source multiplicities are retained.
The logarithmic scratch region is reused for each input element.
-/

namespace ThreeSum.LightResidues
open _root_.ThreeSum.LightResidues


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



theorem residue_cast {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (_root_.ThreeSum.LightResidues.residue p c x : ℤ) = (c * x) % (p : ℤ) := by
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by exact_mod_cast hp.ne')

















end ThreeSum.LightResidues

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual contiguous buckets from a generic residue-code array

This fixed program constructs its own count histogram, then exact prefix
offsets and an index scatter. No caller-supplied bucket lengths or lists are
assumed. It is shared by source extraction and output-sensitive residue joins.
-/

namespace ThreeSum.LightSourceBucketBuild
open _root_.ThreeSum.LightSourceBucketBuild


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000







variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









theorem time_bound (N M : ℕ) : _root_.ThreeSum.LightSourceBucketBuild.time N M ≤ 300*(N+M+1) := by
  unfold _root_.ThreeSum.LightSourceBucketBuild.time _root_.ThreeSum.LightHistogram.histogramTime _root_.ThreeSum.LightHistogram.countTime _root_.Light.fillTime _root_.ThreeSum.LightSourceBucketFromHistogram.time
    _root_.ThreeSum.LightSourceBucketOffsets.time _root_.ThreeSum.LightSourceBucketScatter.time
  omega

end ThreeSum.LightSourceBucketBuild

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
# Actual vertex and trimmed-bucket scales

The local prime and bucket cap are the computable finite selections from
`LocalCoverBounds`.  Their logarithmic rates are derived from those exact
definitions and the exact integer schedule in `Scales`.
-/

namespace ThreeSum.TrimScales
open _root_.ThreeSum.TrimScales


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open scoped _root_.Topology

















noncomputable section





























theorem localLength_pos (h : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength h := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength, _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule_length]
  positivity



























end

end ThreeSum.TrimScales

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
# An actual minimum scan of the fast cyclic correlation

The returned offset obeys the exact mean bound for the supplied histograms.
The choice is made by a fixed program, not by an existential witness in the
proof. The histograms themselves are the procedure's array inputs.
-/

namespace ThreeSum.LightBalancedOffset
open _root_.ThreeSum.LightBalancedOffset


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba
open _root_.ThreeSum.CyclicFold
open _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold
open _root_.ThreeSum.LightKaratsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
open _root_.Finset
open scoped _root_.BigOperators





theorem offset_balanced {p : ℕ} [NeZero p] (F H : ZMod p → ℕ) :
    p * _root_.ThreeSum.Balancing.correlation F H (_root_.ThreeSum.LightBalancedOffset.offset F H : ZMod p) ≤
      (∑ z, F z) * (∑ z, H z) := by
  obtain ⟨z, hz⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.Balancing.exists_balanced_offset F H
  have hmin := _root_.ThreeSum.LightMinimum.least_value_le
    (fun r => (_root_.ThreeSum.Balancing.correlation F H (r : ZMod p) : ℤ)) p z.val (ZMod.val_lt z)
  have hminNat : _root_.ThreeSum.Balancing.correlation F H (_root_.ThreeSum.LightBalancedOffset.offset F H : ZMod p) ≤
      _root_.ThreeSum.Balancing.correlation F H z := by
    simpa only [_root_.ThreeSum.LightBalancedOffset.offset, ZMod.natCast_zmod_val, Nat.cast_le] using hmin
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  rw [hcard] at hz
  exact (Nat.mul_le_mul_left p hminNat).trans hz





variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}











end ThreeSum.LightBalancedOffset

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original integers to a padded signed histogram

The executable procedure first computes canonical residues of the signed
original integers and then fills the entire requested histogram capacity.
Its postcondition is the precise padded polynomial vector consumed by the
verified cyclic-convolution routine. Repeated input values remain distinct
incidences and contribute their full multiplicity.
-/

namespace ThreeSum.LightResidueHistogram
open _root_.ThreeSum.LightResidueHistogram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram
open _root_.ThreeSum.CyclicFold
open _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





theorem sum_signedHistogram {p : ℕ} [NeZero p]
    (c : ℤ) (values : ℕ → ℤ) (n : ℕ) :
    (∑ z : ZMod p, _root_.ThreeSum.LightResidueHistogram.signedHistogram p c values n z) = n := by
  unfold _root_.ThreeSum.LightResidueHistogram.signedHistogram
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Histograms.sum_histogram]
  simp



























end ThreeSum.LightResidueHistogram

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Packed generic residue buckets from four scalar arguments

Only the code-array base, item count, positive residue count, and free pointer are
supplied. The program computes every histogram/offset/cursor/index address
and returns the next free address. Its exact fibers serve both source
reporting and the wanted-record residue join.
-/

namespace ThreeSum.LightSourceBucketSetup
open _root_.ThreeSum.LightSourceBucketSetup


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000













variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









theorem time_bound (N M : ℕ) : _root_.ThreeSum.LightSourceBucketSetup.time N M ≤ 500*(N+M+1) := by
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketBuild.time_bound N M
  unfold _root_.ThreeSum.LightSourceBucketSetup.time
  omega

end ThreeSum.LightSourceBucketSetup

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-input residue keys with a carry offset

The source histogram uses `(x % p + shift) % m`, with two independently
chosen moduli. This procedure computes both remainders from each original
signed input and retains every incidence, including duplicate values.
-/

namespace ThreeSum.LightSourceResidues
open _root_.ThreeSum.LightSourceResidues


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

















variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









theorem time_bound (n p U D : ℕ) :
    _root_.ThreeSum.LightSourceResidues.time n p U D ≤
      254*n*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+6 := by
  unfold _root_.ThreeSum.LightSourceResidues.time _root_.ThreeSum.LightResidues.residueBudget
  nlinarith

end ThreeSum.LightSourceResidues

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



















theorem row_length (n g owner : ℕ) (r : _root_.ThreeSum.BandCandidateRows.Record) :
    (_root_.ThreeSum.BandRawA.row n g owner r).length=if r.flag=1 then _root_.ThreeSum.BandRawA.bandLength n g r.a else 0 := by
  unfold _root_.ThreeSum.BandRawA.row
  split_ifs <;> simp

theorem row_length_le (n g owner : ℕ) (r : _root_.ThreeSum.BandCandidateRows.Record) : (_root_.ThreeSum.BandRawA.row n g owner r).length ≤ g := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.row_length]
  split_ifs
  · exact _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.length_le n g r.a
  · omega





theorem firstRows_succ (n g : ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (i : ℕ) :
    _root_.ThreeSum.BandRawA.firstRows n g rs (i+1)=_root_.ThreeSum.BandRawA.firstRows n g rs i++_root_.ThreeSum.BandRawA.row n g i (rs.getD i default) := by
  simp only [_root_.ThreeSum.BandRawA.firstRows,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]



theorem count_succ (n g : ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (i : ℕ) :
    _root_.ThreeSum.BandRawA.count n g rs (i+1)=_root_.ThreeSum.BandRawA.count n g rs i+(_root_.ThreeSum.BandRawA.row n g i (rs.getD i default)).length := by
  simp only [_root_.ThreeSum.BandRawA.count,_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.firstRows_succ,List.length_append]



theorem count_bound (n g : ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) (i : ℕ) : _root_.ThreeSum.BandRawA.count n g rs i ≤ g*i := by
  induction i with
  | zero => simp [_root_.ThreeSum.BandRawA.count,_root_.ThreeSum.BandRawA.firstRows]
  | succ i ih =>
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.count_succ]
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.row_length_le n g i (rs.getD i default)
    nlinarith

theorem items_length_le (n g : ℕ) (rs : List _root_.ThreeSum.BandCandidateRows.Record) : (_root_.ThreeSum.BandRawA.items n g rs).length ≤ g*rs.length :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.count_bound n g rs rs.length







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



theorem values_bounded {n g i U : ℕ} {rs : List _root_.ThreeSum.BandCandidateRows.Record} {f : ℕ → ℤ}
    (hf : ∀ j < n, |f j| ≤ (U : ℤ)) :
    ∀ v ∈ _root_.ThreeSum.BandRawA.values f (_root_.ThreeSum.BandRawA.firstRows n g rs i), |v| ≤ (U : ℤ) := by
  intro v hv
  obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hv
  exact hf l.position (_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.position_lt hl)









end ThreeSum.BandRawA

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-input histograms give the exact independently trimmed sources

The histogram keys retain the first modular reduction and the signed carry
offset. Looking up the endpoint's final residue therefore counts precisely
the original divisibility condition in `BlockEncoding`. An explicit finite
enumeration accounts for every original input incidence once.
-/

namespace ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.BlockSourceEncoding


open _root_.Finset
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightSourceResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
open scoped _root_.BigOperators

set_option maxHeartbeats 1000000









theorem modulus_pos (h J : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J := pow_pos (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h) J



section OriginalSources

variable {β : Type*} [DecidableEq β]





end OriginalSources

end ThreeSum.BlockSourceEncoding

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
# An actual common offset from two original signed key arrays

The fixed program builds both padded histograms, including reversal, from
the supplied integer keys. It computes its own power-of-two capacity and
chooses the least correlation minimum with the checked fast multiplication.
Repeated keys count separately. No histogram or capacity table is supplied.
-/

namespace ThreeSum.LightOriginalOffset
open _root_.ThreeSum.LightOriginalOffset


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
open _root_.ThreeSum.LightResidueHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
open _root_.ThreeSum.KaratsubaInterface
open _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
open _root_.ThreeSum.CyclicFold
open _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold
open scoped _root_.BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000





/-- The actual selected offset satisfies the exact raw-incidence mean bound,
including duplicate keys in either original array. -/
theorem selected_pairMass_bound (p : ℕ) [NeZero p] (left right : ℕ → ℤ)
    (nLeft nRight : ℕ) :
    p * _root_.ThreeSum.Histograms.pairMass (Finset.range nLeft) (Finset.range nRight)
      (fun i => (left i : ZMod p)) (fun i => (right i : ZMod p))
      (fun _ => 1) (fun _ => 1) (_root_.ThreeSum.LightOriginalOffset.selected p left right nLeft nRight : ZMod p) ≤
        nLeft*nRight := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.LightBalancedOffset.offset_balanced (_root_.ThreeSum.LightResidueHistogram.signedHistogram p 1 right nRight)
    (_root_.ThreeSum.LightResidueHistogram.signedHistogram p 1 left nLeft)
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.sum_signedHistogram,_root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.sum_signedHistogram] at h
  change p * _root_.ThreeSum.Balancing.correlation _ _ (_root_.ThreeSum.LightOriginalOffset.selected p left right nLeft nRight : ZMod p) ≤ _ at h
  unfold _root_.ThreeSum.LightResidueHistogram.signedHistogram at h
  rw [_root_.ThreeSum.Histograms.correlation_histograms] at h
  simpa only [one_mul,Nat.mul_comm] using h









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}













end ThreeSum.LightOriginalOffset

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

/-! # Packed original-band histograms and exact physical residue fibers -/

namespace ThreeSum.SourceBandLayout
open _root_.ThreeSum.SourceBandLayout


open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets


















theorem capacity_product_le (n g : ℕ) (hg : 0 < g) : _root_.ThreeSum.BandPartition.size n g*_root_.ThreeSum.SourceBandLayout.cap n g ≤ 2*n := by
  by_cases hgn : g ≤ n
  · rw [_root_.ThreeSum.SourceBandLayout.cap,min_eq_right hgn]
    exact (_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mul_le n g).trans (by omega)
  · by_cases hn : n=0
    · simp [hn,_root_.ThreeSum.SourceBandLayout.cap]
    · have hdiv : (n-1)/g=0 := Nat.div_eq_of_lt (by omega)
      simp only [_root_.ThreeSum.SourceBandLayout.cap,min_eq_left (by omega : n ≤ g),_root_.ThreeSum.BandPartition.size,if_neg hn,hdiv,zero_add,one_mul]
      omega













theorem work_bound (base n g m : ℕ) (hg : 0 < g) :
    _root_.ThreeSum.SourceBandLayout.work base n g m ≤ base+4*n+_root_.ThreeSum.BandPartition.size n g*(3*m+7) := by
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.capacity_product_le n g hg
  unfold _root_.ThreeSum.SourceBandLayout.work _root_.ThreeSum.SourceBandLayout.hist _root_.ThreeSum.SourceBandLayout.data _root_.ThreeSum.SourceBandLayout.stride
  nlinarith













end ThreeSum.SourceBandLayout

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









theorem occurrence_card (h J : ℕ) : Fintype.card (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h^J := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence,Fintype.card_fun,Fintype.card_fin]

theorem occurrence_card_eq_scheduleCount (n : ℕ) :
    Fintype.card (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))) = _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.occurrence_card,_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount,_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.replicatedHalf,_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize_eq_length]

theorem width_eq (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)*(464*_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) = 232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize _root_.ThreeSum.Scales.microSize _root_.ThreeSum.Scales.microHalf
  ring

theorem cutoff_eq (n : ℕ) :
    2*_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) = _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize _root_.ThreeSum.Scales.microSize _root_.ThreeSum.Scales.microHalf
  ring

















end ThreeSum.BlockSourceSharing

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The actual array-selected offset balances original output records

The program's right histogram is indexed by literal key-array positions.
This module transports that count bijectively to the original global output
type, retaining distinct outputs that happen to have equal integer keys.
-/

namespace ThreeSum.GlobalKeyOffset
open _root_.ThreeSum.GlobalKeyOffset


open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open scoped _root_.BigOperators

set_option maxHeartbeats 1800000

















theorem residue_relation_iff (p : ℕ) (left right d : ℤ) :
    (right : ZMod p)-(left : ZMod p)=(d : ZMod p) ↔ (p : ℤ) ∣ left+d-right := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_sub,Int.cast_add,sub_eq_zero]
  constructor
  · intro hh
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp hh).symm
  · intro hh
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using hh.symm



end ThreeSum.GlobalKeyOffset

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



theorem global_length (h J : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalKeys h J).length=_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount h^J := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalKeys_length,_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount,mul_pow]















end ThreeSum.LightCoverKeyData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Two retained original-band catalogs and one shared empty histogram -/

namespace ThreeSum.SourceBandPairData
open _root_.ThreeSum.SourceBandPairData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition






theorem work_ge (base n g m : ℕ) : base ≤ _root_.ThreeSum.SourceBandLayout.work base n g m := by
  unfold _root_.ThreeSum.SourceBandLayout.work _root_.ThreeSum.SourceBandLayout.hist _root_.ThreeSum.SourceBandLayout.data
  omega

theorem ordered (base NL NR g m : ℕ) :
    _root_.ThreeSum.SourceBandPairData.leftBase base ≤ _root_.ThreeSum.SourceBandPairData.rightBase base NL g m ∧
    _root_.ThreeSum.SourceBandPairData.rightBase base NL g m ≤ _root_.ThreeSum.SourceBandPairData.zeroBase base NL NR g m ∧
    _root_.ThreeSum.SourceBandPairData.zeroBase base NL NR g m < _root_.ThreeSum.SourceBandPairData.next base NL NR g m := by
  exact ⟨_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.work_ge _ _ _ _,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.work_ge _ _ _ _,by unfold _root_.ThreeSum.SourceBandPairData.next; omega⟩















end ThreeSum.SourceBandPairData

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
# Exact shared-bank dimensions and charge of the actual catalog

There are two stage families for each original band and occurrence vector.
The decoder and bank-loop overhead are included. Neither the number of
complete output subsets nor the three-valued query lift multiplies this
construction.
-/

namespace ThreeSum.BlockSourceCatalogCosts
open _root_.ThreeSum.BlockSourceCatalogCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout

theorem count_eq_scheduleCount (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) =
      _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.occurrence_card,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.occurrence_card_eq_scheduleCount]























end ThreeSum.BlockSourceCatalogCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retained common-prime metadata for one actual color execution -/

namespace ThreeSum.EncodedColorPrimeData
open _root_.ThreeSum.EncodedColorPrimeData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light









theorem Stored.heads_read {μ : ℕ → ℤ} {free M y : ℕ} {qs : ℕ → ℕ} (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeData.Stored μ free M y qs) :
    μ free=(qs (_root_.ThreeSum.LightBandPrimeDepth.depth M y) : ℤ) ∧
    μ (free+1)=(_root_.ThreeSum.LightBandPrimeDepth.depth M y : ℤ) ∧
    μ (free+2)=(_root_.ThreeSum.EncodedColorPrimeData.nextFree free M y : ℤ) ∧
    μ (free+3)=(_root_.ThreeSum.EncodedColorPrimeData.poolBase free : ℤ) ∧
    μ (free+4)=(_root_.ThreeSum.LightPrimePool.size y : ℤ) ∧
    μ (free+5)=(_root_.ThreeSum.EncodedColorPrimeData.prefixBase free y : ℤ) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa [_root_.ThreeSum.EncodedColorPrimeData.values] using H.header.getD (i := 0) (by simp [_root_.ThreeSum.EncodedColorPrimeData.values]) 0
  · simpa [_root_.ThreeSum.EncodedColorPrimeData.values] using H.header.getD (i := 1) (by simp [_root_.ThreeSum.EncodedColorPrimeData.values]) 0
  · simpa [_root_.ThreeSum.EncodedColorPrimeData.values] using H.header.getD (i := 2) (by simp [_root_.ThreeSum.EncodedColorPrimeData.values]) 0
  · simpa [_root_.ThreeSum.EncodedColorPrimeData.values] using H.header.getD (i := 3) (by simp [_root_.ThreeSum.EncodedColorPrimeData.values]) 0
  · simpa [_root_.ThreeSum.EncodedColorPrimeData.values] using H.header.getD (i := 4) (by simp [_root_.ThreeSum.EncodedColorPrimeData.values]) 0
  · simpa [_root_.ThreeSum.EncodedColorPrimeData.values] using H.header.getD (i := 5) (by simp [_root_.ThreeSum.EncodedColorPrimeData.values]) 0



end ThreeSum.EncodedColorPrimeData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original A positions and all three guarded lifts

The physical key order is lift-major, preserving every original position.
The selected-offset count is transported to the unchanged guarded wanted
labels used by raw reporting, including repeated input values.
-/

namespace ThreeSum.RawAKeyLists
open _root_.ThreeSum.RawAKeyLists


open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open scoped _root_.BigOperators

set_option maxHeartbeats 900000















theorem keys_length (P : ℤ) (xs : List ℤ) : (_root_.ThreeSum.RawAKeyLists.keys P xs).length=3*xs.length := by
  rw [_root_.ThreeSum.RawAKeyLists.keys,List.length_map,_root_.ThreeSum.RawAKeyLists.records_length]

































end ThreeSum.RawAKeyLists

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Padded histogram selection for independently chosen original bands -/

namespace ThreeSum.SourceBandPairSlices
open _root_.ThreeSum.SourceBandPairSlices


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.SourceBandLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
open _root_.ThreeSum.SourceBandPairData
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData



















theorem heads_read {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g p m : ℕ} {shift : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.Stored μ fL fR base NL NR g p m shift) :
    μ base=(_root_.ThreeSum.SourceBandPairData.leftBase base : ℤ) ∧ μ (base+1)=(_root_.ThreeSum.BandPartition.size NL g : ℤ) ∧
    μ (base+2)=(_root_.ThreeSum.SourceBandPairData.rightBase base NL g m : ℤ) ∧ μ (base+3)=(_root_.ThreeSum.BandPartition.size NR g : ℤ) ∧
    μ (base+4)=(_root_.ThreeSum.SourceBandPairData.zeroBase base NL NR g m : ℤ) ∧ μ (base+5)=(_root_.ThreeSum.SourceBandPairData.next base NL NR g m : ℤ) ∧
    μ (base+6)=(NL : ℤ) ∧ μ (base+7)=(NR : ℤ) := by
  exact ⟨by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 0) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0,
    by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 1) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0,
    by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 2) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0,
    by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 3) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0,
    by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 4) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0,
    by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 5) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0,
    by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 6) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0,
    by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 7) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0⟩

end ThreeSum.SourceBandPairSlices

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # One compact retained layout for a selected color -/

namespace ThreeSum.EncodedColorLayout
open _root_.ThreeSum.EncodedColorLayout





















theorem normalized_ends_before_count (free n g : ℕ) :
    _root_.ThreeSum.EncodedColorLayout.av free n+n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧ _root_.ThreeSum.EncodedColorLayout.ae free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧
    _root_.ThreeSum.EncodedColorLayout.bv free n+n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧ _root_.ThreeSum.EncodedColorLayout.be free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧
    _root_.ThreeSum.EncodedColorLayout.cv free n+n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧ _root_.ThreeSum.EncodedColorLayout.ce free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧
    _root_.ThreeSum.EncodedColorLayout.tables free n+_root_.ThreeSum.ColorBandBounds.count n g ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ∧
    _root_.ThreeSum.EncodedColorLayout.rec free n g+4*_root_.ThreeSum.ColorBandBounds.count n g ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g := by
  unfold _root_.ThreeSum.EncodedColorLayout.normalizedEnd _root_.ThreeSum.LightBandRawA.space _root_.ThreeSum.LightBandRawA.positionBase _root_.ThreeSum.LightBandRawA.ownerBase
    _root_.ThreeSum.LightBandRawA.capacity _root_.ThreeSum.EncodedColorLayout.vals _root_.ThreeSum.EncodedColorLayout.rec _root_.ThreeSum.EncodedColorLayout.tables _root_.ThreeSum.EncodedColorLayout.ce _root_.ThreeSum.EncodedColorLayout.cv _root_.ThreeSum.EncodedColorLayout.be _root_.ThreeSum.EncodedColorLayout.bv _root_.ThreeSum.EncodedColorLayout.ae _root_.ThreeSum.EncodedColorLayout.av
  omega







theorem prime_le_cover (free n g M y : ℕ) : _root_.ThreeSum.EncodedColorLayout.prime free n g+6 ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y := by
  unfold _root_.ThreeSum.EncodedColorLayout.cover _root_.ThreeSum.EncodedColorPrimeData.nextFree _root_.ThreeSum.EncodedColorPrimeData.prefixBase _root_.ThreeSum.EncodedColorPrimeData.poolBase
  omega

theorem normalized_ends_cover (free n g M y : ℕ) :
    _root_.ThreeSum.EncodedColorLayout.av free n+n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧ _root_.ThreeSum.EncodedColorLayout.ae free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧
    _root_.ThreeSum.EncodedColorLayout.bv free n+n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧ _root_.ThreeSum.EncodedColorLayout.be free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧
    _root_.ThreeSum.EncodedColorLayout.cv free n+n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧ _root_.ThreeSum.EncodedColorLayout.ce free n+2+2*n ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧
    _root_.ThreeSum.EncodedColorLayout.tables free n+_root_.ThreeSum.ColorBandBounds.count n g ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧
    _root_.ThreeSum.EncodedColorLayout.rec free n g+4*_root_.ThreeSum.ColorBandBounds.count n g ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y ∧
    _root_.ThreeSum.LightBandRawA.space (_root_.ThreeSum.EncodedColorLayout.vals free n g) (_root_.ThreeSum.ColorBandBounds.count n g) g ≤ _root_.ThreeSum.EncodedColorLayout.cover free n g M y := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout.normalized_ends_before_count free n g
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout.prime_le_cover free n g M y
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g ≤ _
  unfold _root_.ThreeSum.EncodedColorLayout.prime at h
  omega

end ThreeSum.EncodedColorLayout

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

theorem four_le_scheduleSize (h : ℕ) : 4 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize _root_.ThreeSum.LocalHashMoments.scheduleLength
  calc
    4 ≤ 320 := by decide
    _ ≤ 320*(2*h+1) := Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)

theorem localPrime_le_four_outputs (h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ 4*_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h := by
  have ho : 2^(2*h) ≤ _root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h := by
    by_cases hz : h=0
    · simp [hz,_root_.ThreeSum.LocalCoverBounds.outputCount]
    · exact (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.concrete_output_gt_pow (by omega)).le
  have hu := _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_sq_upper h
  have hm := Nat.mul_le_mul_left (16*_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h) ho
  nlinarith

theorem modulus_le_global_outputs (h J : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h^J*
      (J*(464*h)).choose (J*(2*h)) := by
  have hl : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h*_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.localPrime_le_four_outputs h).trans (Nat.mul_le_mul_right _ (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.four_le_scheduleSize h))
  have hp := Nat.pow_le_pow_left hl J
  rw [mul_pow] at hp
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus
  exact hp.trans (Nat.mul_le_mul_left _ (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.choose_pow_le (464*h) (2*h) J))

theorem modulus_le_tableCount (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.tableCount n := by
  have hm := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.modulus_le_global_outputs (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))
  have hc : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)*(2*_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n))=_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
    rw [Nat.mul_comm,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.cutoff_eq]
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.width_eq,hc] at hm
  change _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n ≥ _ at hm
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts.count_eq_scheduleCount] at hm
  exact hm

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

theorem scheduleCount_pos (n : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.replicatedHalf
  exact pow_pos (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength_pos _) _

theorem bands_outputs_le_encoderCount (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := by
  have hs : 1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.scheduleCount_pos n
  calc
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_right (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n) (Nat.mul_le_mul_left (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n) hs)
    _ ≤ 2*(_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n) := Nat.le_mul_of_pos_left _ (by omega)
    _ = _ := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount; ring

theorem input_le_encoderCount (n : ℕ) : n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := by
  calc
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n := (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount_mul_bounds n).1
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n := Nat.mul_le_mul_right _ (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.bandSize_le_fullOutputs n)
    _ = _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n := Nat.mul_comm _ _
    _ ≤ _ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.bands_outputs_le_encoderCount n

theorem bands_modulus_le_encoderCount (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := by
  calc
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.tableCount n := Nat.mul_le_mul_left _ (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.modulus_le_tableCount n)
    _ ≤ 2*(_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.tableCount n) := Nat.le_mul_of_pos_left _ (by omega)
    _ = _ := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.tableCount _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount; ring

theorem bands_le_encoderCount (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := by
  calc
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) :=
      Nat.le_mul_of_pos_right _ (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus_pos _ _)
    _ ≤ _ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.bands_modulus_le_encoderCount n

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



theorem persistent_space_le_encoderCount {base N n : ℕ} (hN : N ≤ n) :
    _root_.ThreeSum.SourceBandLayout.work base N (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))) ≤
      base+14*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := by
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.work_bound base N (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n)
  have hn := hN.trans (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.input_le_encoderCount n)
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.size_le_bandCount hN
  have hm := (Nat.mul_le_mul_right
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))) hb).trans
      (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.bands_modulus_le_encoderCount n)
  have hbc := hb.trans (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.bands_le_encoderCount n)
  nlinarith

end ThreeSum.SourceBandCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact output-sensitive residue join semantics

The join visits a stored right-index fiber once for each left input
position. Its output is the literal list of matching position pairs.
The count is the guarded wanted mass when the left codes include the
selected common shift and the right codes are the original output keys.
-/

namespace ThreeSum.WantedPairs
open _root_.ThreeSum.WantedPairs


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open scoped _root_.BigOperators

set_option maxHeartbeats 1200000



@[simp] theorem count_zero (left right : ℕ → ℕ) (NR : ℕ) : _root_.ThreeSum.WantedPairs.count left right NR 0=0 := by
  simp [_root_.ThreeSum.WantedPairs.count]

theorem count_succ (left right : ℕ → ℕ) (NR n : ℕ) :
    _root_.ThreeSum.WantedPairs.count left right NR (n+1)=_root_.ThreeSum.WantedPairs.count left right NR n+_root_.ThreeSum.LightHistogram.count right (left n) NR :=
  Finset.sum_range_succ _ _



























theorem residue_eq_iff {M : ℕ} (hM : 0 < M) (a b d : ℤ) :
    _root_.ThreeSum.LightResidues.residue M 1 b=_root_.ThreeSum.LightResidues.residue M 1 (a+d) ↔ (M : ℤ) ∣ a+d-b := by
  rw [← Nat.cast_inj (R := ℤ),_root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_cast hM,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_cast hM,one_mul,one_mul]
  exact Int.modEq_iff_dvd







end ThreeSum.WantedPairs

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A literal output-sensitive join of original-position residue arrays

The host reads each left code and visits only its matching retained right
fiber. Recursion gives a sum of actual row costs; it never charges or scans
the full left/right Cartesian product. The output contains every matching
original-position pair exactly once.
-/

namespace ThreeSum.LightWantedJoin
open _root_.ThreeSum.LightWantedJoin


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.WantedPairs
open _root_.ThreeSum1960614.Machine.ThreeSum.WantedPairs

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000





theorem time_bound (left right : ℕ → ℕ) (NR n : ℕ) :
    _root_.ThreeSum.LightWantedJoin.time left right NR n ≤ 400*(n+_root_.ThreeSum.WantedPairs.count left right NR n+1) := by
  induction n with
  | zero => simp [_root_.ThreeSum.LightWantedJoin.time]
  | succ n ih => rw [_root_.ThreeSum.LightWantedJoin.time,_root_.ThreeSum1960614.Machine.ThreeSum.WantedPairs.count_succ]; unfold _root_.ThreeSum.LightWantedRow.time; omega

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}







end ThreeSum.LightWantedJoin

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Finite cost of both actual original-band catalogs and empty padding -/

namespace ThreeSum.SourceBandPairCosts
open _root_.ThreeSum.SourceBandPairCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.SourceBandPairData
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData





theorem tableCount_le_encoderCount {n : ℕ} (hn : 0 < n) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.tableCount n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := by
  have hb : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n := by
    have hp := (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount_mul_bounds n).1
    by_contra h
    have hz : _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n=0 := by omega
    rw [hz,Nat.mul_zero] at hp
    omega
  calc
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.tableCount n := Nat.le_mul_of_pos_left _ hb
    _ ≤ 2*(_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.tableCount n) := Nat.le_mul_of_pos_left _ (by omega)
    _ = _ := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.tableCount _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount; ring

theorem modulus_le_encoderCount {n : ℕ} (hn : 0 < n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.modulus_le_tableCount n).trans (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairCosts.tableCount_le_encoderCount hn)



theorem next_le_encoderCount {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    _root_.ThreeSum.SourceBandPairData.next base NL NR (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))) ≤
      base+29*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n+9 := by
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.persistent_space_le_encoderCount (base := _root_.ThreeSum.SourceBandPairData.leftBase base) hNL
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.persistent_space_le_encoderCount
    (base := _root_.ThreeSum.SourceBandPairData.rightBase base NL (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))) hNR
  have hm := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairCosts.modulus_le_encoderCount hn
  change _root_.ThreeSum.SourceBandPairData.rightBase base NL (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) _ ≤ _ at hl
  change _root_.ThreeSum.SourceBandPairData.zeroBase base NL NR (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) _ ≤ _ at hr
  unfold _root_.ThreeSum.SourceBandPairData.next _root_.ThreeSum.SourceBandPairData.leftBase at *
  omega

end ThreeSum.SourceBandPairCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The actual residue scans and the selected wanted mass

The two-remainder source scanner specializes to an ordinary shifted residue
when its moduli agree. Its actual fiber count is exactly the incidence mass
minimized by the original signed-array offset program.
-/

namespace ThreeSum.WantedResidueKeys
open _root_.ThreeSum.WantedResidueKeys


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open scoped _root_.BigOperators



theorem code_eq_residue (M : ℕ) (shift x : ℤ) :
    _root_.ThreeSum.WantedResidueKeys.code M shift x=_root_.ThreeSum.LightResidues.residue M 1 (x+shift) := by
  simp only [_root_.ThreeSum.WantedResidueKeys.code,_root_.ThreeSum.LightSourceResidues.key,_root_.ThreeSum.LightResidues.residue,one_mul]
  congr 1
  rw [Int.add_emod,Int.emod_emod,← Int.add_emod]



theorem code_eq_iff {M : ℕ} (hM : 0 < M) (a b shift : ℤ) :
    _root_.ThreeSum.WantedResidueKeys.code M 0 b=_root_.ThreeSum.WantedResidueKeys.code M shift a ↔ (M : ℤ) ∣ a+shift-b := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys.code_eq_residue,_root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys.code_eq_residue,add_zero]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.WantedPairs.residue_eq_iff hM a b shift



theorem total_eq_pairMass (M : ℕ) (hM : 0 < M) (left right : ℕ → ℤ)
    (NL NR : ℕ) (shift : ℤ) :
    _root_.ThreeSum.WantedResidueKeys.total M left right NL NR shift =
      _root_.ThreeSum.Histograms.pairMass (Finset.range NL) (Finset.range NR)
        (fun i => (left i : ZMod M)) (fun j => (right j : ZMod M))
        (fun _ => 1) (fun _ => 1) (shift : ZMod M) := by
  unfold _root_.ThreeSum.WantedResidueKeys.total _root_.ThreeSum.WantedPairs.count _root_.ThreeSum.LightHistogram.count _root_.ThreeSum.Histograms.pairMass
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,one_mul,
    _root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys.code_eq_iff hM,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyOffset.residue_relation_iff]

theorem selected_total_bound (M : ℕ) [NeZero M] (left right : ℕ → ℤ) (NL NR : ℕ) :
    M*_root_.ThreeSum.WantedResidueKeys.total M left right NL NR (_root_.ThreeSum.LightOriginalOffset.selected M left right NL NR) ≤ NL*NR := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys.total_eq_pairMass M (Nat.pos_of_ne_zero (NeZero.ne M))]
  simpa only [Int.cast_natCast] using _root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset.selected_pairMass_bound M left right NL NR





end ThreeSum.WantedResidueKeys

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original signed arrays to an actual shifted wanted-pair array

The closed host computes all residue and bucket addresses, runs both signed
scans, builds the right fibers, and executes the output-sensitive join. Four
header cells retain the pair count, pair-array address, next free address and
the actual shift. No residue array, histogram or matching list is supplied.
-/

namespace ThreeSum.LightWantedSetup
open _root_.ThreeSum.LightWantedSetup


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.WantedResidueKeys
open _root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000






















variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}



theorem time_bound (M : ℕ) (left right : ℕ → ℤ) (NL NR U D : ℕ) (shift : ℤ) :
    _root_.ThreeSum.LightWantedSetup.time M left right NL NR U D shift ≤
      2000*(NL+NR+M+_root_.ThreeSum.WantedResidueKeys.total M left right NL NR shift+1)*
        (Nat.log 2 (U+1)+Nat.log 2 (M+D+1)+1) := by
  have hL := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.time_bound NL M U D
  have hR := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.time_bound NR M U D
  have hB := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSetup.time_bound NR M
  have hJ := _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedJoin.time_bound (fun i => _root_.ThreeSum.WantedResidueKeys.code M shift (left i))
    (fun j => _root_.ThreeSum.WantedResidueKeys.code M 0 (right j)) NR NL
  change _root_.ThreeSum.LightWantedJoin.time _ _ NR NL ≤ 400*(NL+_root_.ThreeSum.WantedResidueKeys.total M left right NL NR shift+1) at hJ
  unfold _root_.ThreeSum.LightWantedSetup.time
  nlinarith

end ThreeSum.LightWantedSetup

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact shared construction counts and finite encoder charge -/

namespace ThreeSum.SourceBandBanksCosts
open _root_.ThreeSum.SourceBandBanksCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress







theorem count_le_bandCount {NL NR n : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    _root_.ThreeSum.SourceBandPairSlices.count NL NR (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n :=
  max_le (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.size_le_bandCount hNL) (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.size_le_bandCount hNR)













theorem finish_eq (base NL NR g h J cut : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish base NL NR g h J cut=
      base+5+_root_.ThreeSum.SourceBandPairSlices.count NL NR g*_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J cut := rfl





theorem finish_le_encoderCount {base NL NR n : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish base NL NR (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) ≤
      base+5+_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts.storageFactor n*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts.finish_eq]
  exact Nat.add_le_add_left (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts.span_count_le_encoderCount (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts.count_le_bandCount hNL hNR)) _



end ThreeSum.SourceBandBanksCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Executable balancing followed by the complete wanted-pair join

The host chooses the common shift from the two original signed arrays and
then builds every matching original-position pair. The returned count obeys
the exact incidence mean bound. The offset and the residue/bucket inputs are
computed by the closed program, with the same duplicate multiplicities.
-/

namespace ThreeSum.LightBalancedWanted
open _root_.ThreeSum.LightBalancedWanted


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.WantedResidueKeys
open _root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000













variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}



theorem total_le_div (M : ℕ) [NeZero M] (left right : ℕ → ℤ) (NL NR : ℕ) :
    _root_.ThreeSum.WantedResidueKeys.total M left right NL NR (_root_.ThreeSum.LightOriginalOffset.selected M left right NL NR) ≤ NL*NR/M := by
  apply (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (NeZero.ne M))).mpr
  simpa only [Nat.mul_comm] using _root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys.selected_total_bound M left right NL NR

theorem time_bound (M : ℕ) [NeZero M] (left right : ℕ → ℤ) (NL NR U : ℕ) :
    _root_.ThreeSum.LightBalancedWanted.time M left right NL NR U ≤ _root_.ThreeSum.LightOriginalOffset.time M NL NR U+
      2000*(NL+NR+M+NL*NR/M+1)*(Nat.log 2 (U+1)+Nat.log 2 (M+M+1)+1)+100 := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.time_bound M left right NL NR U M
    (_root_.ThreeSum.LightOriginalOffset.selected M left right NL NR)
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightBalancedWanted.total_le_div M left right NL NR
  calc
    _root_.ThreeSum.LightBalancedWanted.time M left right NL NR U ≤ _root_.ThreeSum.LightOriginalOffset.time M NL NR U+
      2000*(NL+NR+M+_root_.ThreeSum.WantedResidueKeys.total M left right NL NR (_root_.ThreeSum.LightOriginalOffset.selected M left right NL NR)+1)*
        (Nat.log 2 (U+1)+Nat.log 2 (M+M+1)+1)+100 := by unfold _root_.ThreeSum.LightBalancedWanted.time; omega
    _ ≤ _ := by gcongr

end ThreeSum.LightBalancedWanted

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Finite resource charge of the actual original-array source host -/

namespace ThreeSum.SourceBandHostCosts
open _root_.ThreeSum.SourceBandHostCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales



theorem scheduleCount_le_encoderCount {n : ℕ} (hn : 0 < n) : _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := by
  have hf : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs n :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.typedOutputs_pos n).trans_le (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.typedOutputs_le_fullOutputs n)
  have hs : _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.tableCount n := Nat.le_mul_of_pos_right _ hf
  exact hs.trans (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairCosts.tableCount_le_encoderCount hn)

theorem occurrenceRows_le_encoderCount {n : ℕ} (hn : 0 < n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts.count_eq_scheduleCount]
  have h := Nat.mul_le_mul_right (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandHostCosts.scheduleCount_le_encoderCount hn)
  simpa only [Nat.mul_comm] using h

theorem bankHeader_le_encoderCount {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.bankHeader base NL NR (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
      (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) ≤
      base+(29+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n+9 := by
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairCosts.next_le_encoderCount (base := base) hn hNL hNR
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandHostCosts.occurrenceRows_le_encoderCount hn
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.bankHeader _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.occurrenceBase
  nlinarith

theorem finish_le_encoderCount {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.finish base NL NR (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
      (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) ≤
      base+(29+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)+_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts.storageFactor n)*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n+14 := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandHostCosts.bankHeader_le_encoderCount (base := base) hn hNL hNR
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts.finish_le_encoderCount
    (base := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.bankHeader base NL NR (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
      (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))) hNL hNR
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.finish
  nlinarith



end ThreeSum.SourceBandHostCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual cover construction, lifted A keys, and balanced wanted records

This closed program runs the local-cover initializer and global key product,
constructs all three lifts of the supplied A incidences, selects the common
offset, and emits precisely the matching position pairs. Every dimension and
output address is read or computed. The retained cover, layers and coefficient
tables are available to the source-bank and output-decoding phases afterwards.
-/

namespace ThreeSum.LightGuardedWanted
open _root_.ThreeSum.LightGuardedWanted


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000




















theorem selected_eq (P M h J : ℕ) [NeZero M] (xs : List ℤ) :
    _root_.ThreeSum.LightOriginalOffset.selected M (_root_.ThreeSum.LightGuardedWanted.left P xs) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right h J) (3*xs.length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J)=
      _root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.selected M P xs h J := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.selected _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyOffset.selected
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.keys_length,_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.global_length]
  rfl





variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}



end ThreeSum.LightGuardedWanted

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Finite cost of computed source controls and their full host -/

namespace ThreeSum.SourceControlCosts
open _root_.ThreeSum.SourceControlCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales









theorem finish_le_encoderCount {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish base NL NR (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
      (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) ≤
      base+(29+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)+_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts.storageFactor n)*_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount n+17 := by
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandHostCosts.finish_le_encoderCount (base := base+3) hn hNL hNR
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish _root_.ThreeSum.LightSourceControlsHost.sourceBase
  omega



end ThreeSum.SourceControlCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Uniform original-size budgets for the finite normalized source host -/

namespace ThreeSum.SourceFiniteCosts
open _root_.ThreeSum.SourceFiniteCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales















theorem finish_le {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish base NL NR (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
      (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.finish base n :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SourceControlCosts.finish_le_encoderCount hn hNL hNR



end ThreeSum.SourceFiniteCosts

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

/-! # Keep the complete finite source catalog below its exact returned end -/

namespace ThreeSum.SourceFiniteData
open _root_.ThreeSum.SourceFiniteData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

theorem source_ends (base NL NR g h J cut : ℕ) :
    base+3 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish base NL NR g h J cut ∧
    _root_.ThreeSum.SourceBandPairData.next (_root_.ThreeSum.LightSourceControlsHost.sourceBase base) NL NR g
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish base NL NR g h J cut ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.bankHeader (_root_.ThreeSum.LightSourceControlsHost.sourceBase base) NL NR g h J+5 ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish base NL NR g h J cut := by
  have ho := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.ordered (_root_.ThreeSum.LightSourceControlsHost.sourceBase base)
    NL NR g (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.finish _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankData.finish
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.baseAt _root_.ThreeSum.SourceBandBankData.first _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.bankHeader
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.occurrenceBase _root_.ThreeSum.LightSourceControlsHost.sourceBase
  unfold _root_.ThreeSum.SourceBandPairData.leftBase _root_.ThreeSum.LightSourceControlsHost.sourceBase at ho
  omega

theorem Stored.of_kept {μ ν : ℕ → ℤ} {base g p h J cut bound : ℕ} {B C : List ℤ} {shift r : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteData.Stored μ base g p h J cut B C shift r)
    (K : _root_.ThreeSum1960614.Machine.Light.Kept μ ν bound)
    (hb : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish base B.length C.length g h J cut ≤ bound) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteData.Stored ν base g p h J cut B C shift r := by
  obtain ⟨hcontrol,hpair,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteData.source_ends base B.length C.length g h J cut
  refine ⟨H.returned,?_,?_,?_⟩
  · exact H.controls.of_kept K (by simpa [_root_.ThreeSum1960614.Machine.ThreeSum.SourceControlLayout.values] using hcontrol.trans hb)
  · exact H.buckets.of_kept (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus_pos h J) K (hpair.trans hb)
  · exact H.banks.of_kept K le_rfl hb

end ThreeSum.SourceFiniteData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact reusable memory boundary after the actual wanted-pair output -/

namespace ThreeSum.EncodedColorWantedData
open _root_.ThreeSum.EncodedColorWantedData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.WantedResidueKeys
open _root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys



theorem header_le_nextFree (out M : ℕ) (left right : ℕ → ℤ) (NL NR : ℕ) (shift : ℤ) :
    out+4 ≤ _root_.ThreeSum.EncodedColorWantedData.nextFree out M left right NL NR shift := by
  unfold _root_.ThreeSum.EncodedColorWantedData.nextFree _root_.ThreeSum.LightWantedSetup.pairBase _root_.ThreeSum.LightSourceBucketSetup.next _root_.ThreeSum.LightWantedSetup.bucketBase
    _root_.ThreeSum.LightWantedSetup.rightCodes _root_.ThreeSum.LightWantedSetup.leftCodes
  omega



theorem of_kept {μ ν : ℕ → ℤ} {out M NL NR bound : ℕ} {left right : ℕ → ℤ} {shift : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output μ out M left right NL NR shift)
    (K : _root_.ThreeSum1960614.Machine.Light.Kept μ ν bound) (hb : _root_.ThreeSum.EncodedColorWantedData.nextFree out M left right NL NR shift ≤ bound) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output ν out M left right NL NR shift := by
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedData.header_le_nextFree out M left right NL NR shift).trans hb
  obtain ⟨hcount,hpair,hnext,hshift,ps,hlen,hnodup,hmem,hrows⟩ := H
  refine ⟨(K _ (by omega)).trans hcount,(K _ (by omega)).trans hpair,
    (K _ (by omega)).trans hnext,(K _ (by omega)).trans hshift,ps,hlen,hnodup,hmem,?_⟩
  apply hrows.of_kept K
  rw [_root_.ThreeSum.WantedPairs.cells_length,hlen]
  exact hb

end ThreeSum.EncodedColorWantedData

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

theorem incidences_length_le {A B C : List ℤ} {n : ℕ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (ha : A.length ≤ n) (hb : B.length ≤ n) (hc : C.length ≤ n) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC).length ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n*_root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences
  rw [_root_.ThreeSum.BandRawA.values_length]
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.items_length_le ..).trans (Nat.mul_le_mul_left _ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.records_length_le ha hb hc))

theorem incidences_bounded {A B C : List ℤ} {n U : ℕ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hA : ∀ j < A.length, |A.getD j 0| ≤ (U : ℤ)) :
    ∀ z ∈ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC, |z| ≤ (U : ℤ) := _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA.values_bounded hA

theorem heads_read {μ : ℕ → ℤ} {free n g : ℕ} (H : _root_.ThreeSum1960614.Machine.Light.Seg μ free (_root_.ThreeSum.EncodedColorLayout.normalizedHeads free n g)) :
    μ free=(_root_.ThreeSum.EncodedColorLayout.av free n : ℤ) ∧ μ (free+1)=(_root_.ThreeSum.EncodedColorLayout.ae free n : ℤ) ∧
    μ (free+2)=(_root_.ThreeSum.EncodedColorLayout.bv free n : ℤ) ∧ μ (free+3)=(_root_.ThreeSum.EncodedColorLayout.be free n : ℤ) ∧
    μ (free+4)=(_root_.ThreeSum.EncodedColorLayout.cv free n : ℤ) ∧ μ (free+5)=(_root_.ThreeSum.EncodedColorLayout.ce free n : ℤ) ∧
    μ (free+6)=(_root_.ThreeSum.EncodedColorLayout.rec free n g : ℤ) ∧ μ (free+7)=(_root_.ThreeSum.EncodedColorLayout.vals free n g : ℤ) := by
  have h (i : ℕ) (hi : i < 8) := H.getD (i := i) (by simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using hi) 0
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 0 (by omega)
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 1 (by omega)
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 2 (by omega)
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 3 (by omega)
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 4 (by omega)
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 5 (by omega)
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 6 (by omega)
  · simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using h 7 (by omega)

end ThreeSum.EncodedColorNormalizedData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Numeric envelopes for the actually balanced wanted records -/

namespace ThreeSum.EncodedColorWantedCosts
open _root_.ThreeSum.EncodedColorWantedCosts


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.WantedResidueKeys
open _root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys

set_option maxHeartbeats 1800000







theorem time_le (P M h J U : ℕ) [NeZero M] (xs : List ℤ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.time P M h J U xs ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.time P M h J U xs.length := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.LightBalancedWanted.time_bound M (_root_.ThreeSum.LightGuardedWanted.left P xs)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right h J) (3*xs.length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.keyBound P h J)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.time _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.time
  omega

theorem sourceBase_eq (free M h J len : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.sourceBase free M h J len=_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd free h J+
      6*len+2*_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J+3*M+5+
      2*(3*len*_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J/M) := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.sourceBase _root_.ThreeSum.LightWantedSetup.pairBase _root_.ThreeSum.LightSourceBucketSetup.next _root_.ThreeSum.LightWantedSetup.bucketBase
    _root_.ThreeSum.LightWantedSetup.rightCodes _root_.ThreeSum.LightWantedSetup.leftCodes _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.wantedFree
  omega

theorem sourceBase_le (free P M h J : ℕ) [NeZero M] (xs : List ℤ) :
    _root_.ThreeSum.EncodedColorWantedData.nextFree (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.wantedFree free h J xs.length) M
      (_root_.ThreeSum.LightGuardedWanted.left P xs) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right h J)
      (3*xs.length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) (_root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.selected M P xs h J) ≤
        _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.sourceBase free M h J xs.length := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.LightBalancedWanted.total_le_div M (_root_.ThreeSum.LightGuardedWanted.left P xs)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right h J) (3*xs.length) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J)
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.selected_eq] at h
  unfold _root_.ThreeSum.EncodedColorWantedData.nextFree _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.sourceBase
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 h) _

theorem space_le (free P M h J U : ℕ) [NeZero M] (xs : List ℤ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.space free P M h J U xs ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.space free P M h J U xs.length := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.sourceBase_le free P M h J xs
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.space _root_.ThreeSum.LightBalancedWanted.space _root_.ThreeSum.LightWantedSetup.space _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.space
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.selected_eq]
  exact max_le_max le_rfl (max_le_max le_rfl (max_le_max le_rfl (max_le_max le_rfl h)))

theorem keyBound_mono {P P' h J : ℕ} (hP : P ≤ P') :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.keyBound P h J ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.keyBound P' h J := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.keyBound
  omega

theorem sourceBase_mono {free M h J len len' : ℕ} (hlen : len ≤ len') :
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.sourceBase free M h J len ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.sourceBase free M h J len' := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.sourceBase_eq,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.sourceBase_eq]
  gcongr

theorem time_mono {P P' M h J U len len' : ℕ} (hP : P ≤ P') (hlen : len ≤ len') :
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.time P M h J U len ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.time P' M h J U len' := by
  have hkey := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.keyBound_mono (h := h) (J := J) hP
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.time _root_.ThreeSum.LightRawAKeys.time _root_.ThreeSum.LightOriginalOffset.time _root_.ThreeSum.LightResidueHistogram.time
    _root_.ThreeSum.LightResidues.residuesTime _root_.ThreeSum.LightResidues.residueBudget _root_.ThreeSum.LightHistogram.histogramTime
    _root_.ThreeSum.LightHistogram.countTime _root_.ThreeSum.LightReportingAffine.time
  gcongr

theorem space_mono {free P P' M h J U len len' : ℕ} (hP : P ≤ P') (hlen : len ≤ len') :
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.space free P M h J U len ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.space free P' M h J U len' := by
  have hkey := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.keyBound_mono (h := h) (J := J) hP
  have hbase := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.sourceBase_mono (free := free) (M := M) (h := h) (J := J) hlen
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.space _root_.ThreeSum.LightRawAKeys.space _root_.ThreeSum.LightOriginalOffset.space _root_.ThreeSum.LightSourceResidues.space
    _root_.ThreeSum.LightWantedSetup.pairBase _root_.ThreeSum.LightSourceBucketSetup.next _root_.ThreeSum.LightWantedSetup.bucketBase
    _root_.ThreeSum.LightWantedSetup.rightCodes _root_.ThreeSum.LightWantedSetup.leftCodes _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.wantedFree
  gcongr

theorem word_mono {P P' M h J U len len' : ℕ} (hP : P ≤ P') (hlen : len ≤ len') :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.word P M h J U len ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.word P' M h J U len' := by
  have hkey := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.keyBound_mono (h := h) (J := J) hP
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.word _root_.ThreeSum.LightRawAKeys.word _root_.ThreeSum.LightBalancedWanted.word
    _root_.ThreeSum.LightOriginalOffset.word _root_.ThreeSum.LightKaratsuba.wordBound _root_.ThreeSum.LightSourceResidues.word
  gcongr

end ThreeSum.EncodedColorWantedCosts

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

/-! # Uniform budgets for wanted records followed by the shared source banks -/

namespace ThreeSum.EncodedColorStageCosts
open _root_.ThreeSum.EncodedColorStageCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds













theorem source_time_mono {n p P U D : ℕ} (hp : p ≤ P) :
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorSourcesCosts.time n p U D ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorSourcesCosts.time n P U D := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorSourcesCosts.time _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.time
  gcongr

theorem source_space_mono {base bound n p P U D : ℕ} (hb : base ≤ bound) (hp : p ≤ P) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.space base n p U D ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.space bound n P U D := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.space
  gcongr

theorem source_word_mono {n p P U D : ℕ} (hp : p ≤ P) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.word n p U D ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.word n P U D := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.word _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.word _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.word
    _root_.ThreeSum.LightSourceBandPair.word _root_.ThreeSum.LightSourceBandStep.word _root_.ThreeSum.LightSourceResidues.word
  gcongr

theorem base_le {free n p M len : ℕ} [NeZero M] {xs : List ℤ} (hlen : xs.length ≤ len) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources.base free n p M xs ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.sourceBase free n M len :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.sourceBase_le free p M (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n))
    (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) xs).trans (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.sourceBase_mono hlen)

theorem time_le {n p P M U len : ℕ} [NeZero M] {xs : List ℤ}
    (hp : p ≤ P) (hlen : xs.length ≤ len) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorWantedSources.time n p M U xs ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.time n P M U len := by
  have hw := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.time_le p M (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n))
    (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) U xs).trans (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.time_mono hp hlen)
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.source_time_mono (n := n) (U := U) (D := M) hp
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorWantedSources.time _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.time
  omega

theorem space_le {free n p P M U len : ℕ} [NeZero M] {xs : List ℤ}
    (hp : p ≤ P) (hlen : xs.length ≤ len) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorWantedSources.space free n p M U xs ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.space free n P M U len := by
  have hw := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.space_le free p M (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n))
    (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) U xs).trans (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.space_mono hp hlen)
  exact max_le_max hw (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.source_space_mono (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.base_le hlen) hp)

theorem word_le {n p P M U len len' : ℕ} (hp : p ≤ P) (hlen : len ≤ len') :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorWantedSources.word n p M U len ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.word n P M U len' :=
  max_le_max (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.word_mono hp hlen) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.source_word_mono hp)

theorem depth_le {n M len len' : ℕ} (hlen : len ≤ len') :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorWantedSources.depth n M len ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.depth n M len' := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.depth _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorWantedSources.depth
  omega

theorem finish_le {base bound NL NR n : ℕ} (hn : 0 < n)
    (hb : base ≤ bound) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish base NL NR (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
      (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.finish bound n := by
  apply (_root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.finish_le hn hNL hNR).trans
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.finish
  omega

theorem selected_le_maxMod {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hR : 4 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n := by
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected_guard (A := A) (B := B) (C := C)
    (hsA := hsA) (hsB := hsB) (hsC := hsC) hR
  have hy := _root_.ThreeSum.Scales.primeWindow_ge_two n
  have hm : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod
    exact Nat.le_mul_of_pos_right _ (by positivity)
  omega

end ThreeSum.EncodedColorStageCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Execute one original color through the retained shared source bank -/

namespace ThreeSum.LightEncodedColorPipeline
open _root_.ThreeSum.LightEncodedColorPipeline


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
open _root_.ThreeSum.EncodedColorLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData

set_option maxHeartbeats 4200000
set_option maxRecDepth 17000

local instance instNeZeroNatRadix (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) := ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩





















variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ}



end ThreeSum.LightEncodedColorPipeline

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
open _root_.ThreeSum.EncodedColorLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
set_option maxHeartbeats 4200000
set_option maxRecDepth 17000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.program_meets__implementation_972ef60e93 {μ : ℕ → ℤ} {src n params row free U : ℕ}
    (color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)) (x : Fin n → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : 0 < n) (hR : 4 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n)
    (hsrc : src+n ≤ free) (hparams : params+19 ≤ free) (hrow : row+6 ≤ free)
    (hspace : _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.space free n U ≤ lim.space) (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.word n U : ℤ) ≤ lim.word)
    (hd : d+_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.depth n ≤ lim.depth)
    (hread : _root_.ThreeSum1960614.Machine.Light.Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (U : ℤ))
    (hparameters : _root_.ThreeSum1960614.Machine.Light.Seg μ params (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values n))
    (hcolor : _root_.ThreeSum1960614.Machine.Light.Seg μ row (_root_.ThreeSum.ColorParameters.fields color)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.program 255 d [src,n,params,row,free] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.time n U)
      (fun r ν => _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Output ν free n color x r ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) := by
  have hsPrime : _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeHost.inputSpace free n U ≤ lim.space := (le_max_left _ _).trans hspace
  have hsStage : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.space (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n) n (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n)
      (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) U (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n) ≤ lim.space :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hspace)
  have hsFinish : _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.finishBound free n+8 ≤ lim.space := (le_max_right _ _).trans ((le_max_right _ _).trans hspace)
  have hsmall (a : ℕ) (ha : a ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.word n U) : (a : ℤ) ≤ lim.word := (Int.ofNat_le.mpr ha).trans hword
  have hwPrime := hsmall (_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeHost.inputWord n U) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.word; omega)
  have hwStage := hsmall (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.word n (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) U
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n)) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.word; omega)
  have hCapWord := hsmall (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.word; omega)
  have hPWord := hsmall (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.word; omega)
  have hMWord := hsmall (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.word; omega)
  have hGWord := hsmall (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.word; omega)
  have hHWord := hsmall (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.word; omega)
  have hJWord := hsmall (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.word; omega)
  have hCutWord := hsmall (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.word; omega)
  have hSWord := hsmall (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))
    (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.word; omega)
  have hdPrime : d+1+_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeHost.depth n ≤ lim.depth := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.depth at hd; omega
  have hdStage : d+1+_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.depth n (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n) ≤
      lim.depth := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.depth at hd; omega
  have add2 : ((free : ℤ)+2).toNat=free+2 := by omega
  have add3 : ((free : ℤ)+3).toNat=free+3 := by omega
  have add4 : ((free : ℤ)+4).toNat=free+4 := by omega
  have add5 : ((free : ℤ)+5).toNat=free+5 := by omega
  have add7 : ((free : ℤ)+7).toNat=free+7 := by omega
  have par1 : ((params : ℤ)+1).toNat=params+1 := by omega
  have par3 : ((params : ℤ)+3).toNat=params+3 := by omega
  have par4 : ((params : ℤ)+4).toNat=params+4 := by omega
  have par14 : ((params : ℤ)+14).toNat=params+14 := by omega
  have par17 : ((params : ℤ)+17).toNat=params+17 := by omega
  have prime2 : ((_root_.ThreeSum.EncodedColorLayout.prime free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) : ℤ)+2).toNat=_root_.ThreeSum.EncodedColorLayout.prime free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)+2 := by omega
  have primePrev : ((_root_.ThreeSum.EncodedColorLayout.prime free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) : ℤ)-1).toNat=_root_.ThreeSum.EncodedColorLayout.normalizedEnd free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) := by
    unfold _root_.ThreeSum.EncodedColorLayout.prime
    omega
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 255) (by rfl : program[255]?=some (body 71 252 253 254))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.body _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.time
  have hPrime := ((_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeHost.program_meets_input (d := d+1) (μ := μ)
    (src := src) (params := params) (row := row) (free := free)
    color x hw hn hR hsrc hparams hrow hsPrime hwPrime hdPrime hread hbound hparameters hcolor).append
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorWantedSources.program.map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate 72))).append
      [_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorWantedHeader.body,_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorResult.body,_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.body 71 252 253 254]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hPrime _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hPrime ?_ ?_ ?_ ?_
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
     on_goal -1 => (rintro ptr μ₁ ⟨hptr, ⟨heads, A, hsA, B, hsB, C, hsC, hcount, normalized, primes⟩, keptPrime⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  let xs := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences n A B C hsA hsB hsC
  let p := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC
  let cover := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.coverBase free n
  let wanted := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.wantedHeader free n xs.length
  let base := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC
  let bank := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC
  let finish := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC
  let occ := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.occurrenceBase (_root_.ThreeSum.LightSourceControlsHost.sourceBase base)
    B.length C.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))
  have ha := _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.length_classList_le color x 0 1
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.length_classList_le color x 1 1
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.length_classList_le color x 2 (-1)
  have hnA := normalized.2.1.2.1.trans ha
  have hnB := normalized.2.2.1.2.1.trans hb
  have hnC := normalized.2.2.2.1.2.1.trans hc
  have hlen : xs.length ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences_length_le hnA hnB hnC
  have hp : 0 < p := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected_pos
  have hmax : p ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.selected_le_maxMod hR
  have hbaseBound : base ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.sourceBound free n := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.base_le hlen
  have hfinishBound : finish ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.finishBound free n := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.finish_le hn hbaseBound hnB hnC
  have hfinishSpace : finish+8 ≤ lim.space := by omega
  obtain ⟨hmeta,hfree,hcover,hwanted,hcontrol,hbank⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  change _root_.ThreeSum.EncodedColorLayout.prime free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)+6 ≤ cover at hmeta
  change free+8 ≤ cover at hfree
  change cover ≤ base at hcover
  change wanted+4 ≤ base at hwanted
  change base+3 ≤ finish at hcontrol
  change bank+5 ≤ finish at hbank
  obtain ⟨hav,hae,hbv,hbe,hcv,hce,htables,hrecords,hcatalog⟩ :=
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout.normalized_ends_cover free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.Scales.primeWindow n)
  change _root_.ThreeSum.EncodedColorLayout.av free n+n ≤ cover at hav
  change _root_.ThreeSum.EncodedColorLayout.ae free n+2+2*n ≤ cover at hae
  change _root_.ThreeSum.EncodedColorLayout.bv free n+n ≤ cover at hbv
  change _root_.ThreeSum.EncodedColorLayout.be free n+2+2*n ≤ cover at hbe
  change _root_.ThreeSum.EncodedColorLayout.cv free n+n ≤ cover at hcv
  change _root_.ThreeSum.EncodedColorLayout.ce free n+2+2*n ≤ cover at hce
  change _root_.ThreeSum.EncodedColorLayout.tables free n+_root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) ≤ cover at htables
  change _root_.ThreeSum.EncodedColorLayout.rec free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)+4*_root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) ≤ cover at hrecords
  change _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) ≤ cover at hcatalog
  have hvals : _root_.ThreeSum.EncodedColorLayout.vals free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)+xs.length ≤ cover := by
    have hle : _root_.ThreeSum.EncodedColorLayout.vals free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)+xs.length ≤ _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) := by
      unfold _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap at hlen
      unfold _root_.ThreeSum.EncodedColorLayout.normalizedEnd _root_.ThreeSum.LightBandRawA.space _root_.ThreeSum.LightBandRawA.positionBase _root_.ThreeSum.LightBandRawA.ownerBase _root_.ThreeSum.LightBandRawA.capacity
      omega
    exact hle.trans hcatalog
  have hActualSpace := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.space_le (free := cover) (U := U) hmax hlen).trans hsStage
  have hActualWord := (Int.ofNat_le.mpr (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.word_le (U := U) hmax hlen)).trans hwStage
  have hActualDepth : d+1+_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorWantedSources.depth n (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) xs.length ≤ lim.depth :=
    (Nat.add_le_add_left (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.depth_le hlen) (d+1)).trans hdStage
  obtain ⟨readP,_,readCover,_,_,_⟩ := primes.heads_read
  change μ₁ (_root_.ThreeSum.EncodedColorLayout.prime free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n))=(p : ℤ) at readP
  change μ₁ (_root_.ThreeSum.EncodedColorLayout.prime free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)+2)=(cover : ℤ) at readCover
  obtain ⟨_,_,readB,readBE,readC,readCE,_,readVals⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.heads_read heads
  have params₁ := hparameters.of_kept keptPrime (by
    simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.values] using hparams)
  obtain ⟨_,readH,readJ,readCut,readM,readG,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorParameterData.reads params₁
  have hlenWord : (xs.length : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hlen).trans hCapWord
  have hpWord : (p : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hmax).trans hPWord
  have hPrevEq : (_root_.ThreeSum.EncodedColorLayout.prime free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) : ℤ)-1=(_root_.ThreeSum.EncodedColorLayout.normalizedEnd free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) : ℤ) := by
    unfold _root_.ThreeSum.EncodedColorLayout.prime
    omega
  have hPrevWord : (_root_.ThreeSum.EncodedColorLayout.normalizedEnd free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) ≤ lim.space by omega)).trans hw
  change μ₁ (_root_.ThreeSum.EncodedColorLayout.normalizedEnd free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n))=(xs.length : ℤ) at hcount
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (p : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hptr, readP]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hptr, readP] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hptr, readP] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (cover : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hptr, prime2, readCover]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hptr, prime2, readCover] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hptr, prime2, readCover] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (xs.length : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hptr, hPrevEq, hcount]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hptr, hPrevEq, hcount] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hptr, hPrevEq, hcount] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.EncodedColorLayout.vals free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readVals, add7]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readVals, add7] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readVals, add7] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.EncodedColorLayout.bv free n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readB, add2]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readB, add2] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readB, add2] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.EncodedColorLayout.be free n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readBE, add3]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readBE, add3] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readBE, add3] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.EncodedColorLayout.cv free n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readC, add4]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readC, add4] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readC, add4] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.EncodedColorLayout.ce free n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readCE, add5]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readCE, add5] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readCE, add5] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readH, par1]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readH, par1] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readH, par1] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readJ, par3]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readJ, par3] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readJ, par3] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readCut, par4]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readCut, par4] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readCut, par4] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readM, par14]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readM, par14] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readM, par14] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, readG, par17]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [readG, par17] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, readG, par17] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hxs : _root_.ThreeSum1960614.Machine.Light.Seg μ₁ (_root_.ThreeSum.EncodedColorLayout.vals free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) xs := normalized.2.2.2.2.2.2.valueRows
  have hclassA := _root_.ThreeSum1960614.Machine.ThreeSum.LightColorBands.class_bounded color x 0 1 (by norm_num) hbound
  have hclassB := _root_.ThreeSum1960614.Machine.ThreeSum.LightColorBands.class_bounded color x 1 1 (by norm_num) hbound
  have hclassC := _root_.ThreeSum1960614.Machine.ThreeSum.LightColorBands.class_bounded color x 2 (-1) (by norm_num) hbound
  have hxsBound : ∀ z ∈ xs, |z| ≤ (U : ℤ) :=
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences_bounded (_root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteInputs.prepared_bound normalized.2.1 hclassA)
  have hSources := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.meets
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorWantedSources.program_meets (d := d+1) (μ := μ₁) (a := _root_.ThreeSum.EncodedColorLayout.vals free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n))
      (free := cover) (p := p) (M := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (U := U) (xs := xs) hw hActualDepth hn hp ha hb hc hvals
      hav hae hbv hbe hcv hce htables hrecords hcatalog hActualSpace hActualWord hxs hxsBound
      hclassB hclassC normalized) _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeHost.program).append
      [_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorWantedHeader.body,_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorResult.body,_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.body 71 252 253 254]
  have hSourcesBound := hSources.mono_time (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.time_le hmax hlen)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hSourcesBound _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hSourcesBound ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorWantedSources.args]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorWantedSources.args] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorWantedSources.args] <;> omega)
     on_goal -1 => (rintro last μ₂ ⟨normalized₂, sources, cover₂, wanted₂, countBound, lifts, keptSources⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hlast : last=(finish : ℤ) := sources.returned
  have hnext : μ₂ (wanted+2)=(base : ℤ) := wanted₂.2.2.1
  have readOcc : μ₂ (base+8)=(occ : ℤ) := by
    simpa [_root_.ThreeSum.LightSourceControlsHost.sourceBase,Nat.add_assoc,occ,_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHost.occurrenceBase,
      base,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.controls,cover,p,xs]
      using (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices.heads_read sources.buckets).2.2.2.2.2.1
  have readS : μ₂ (base+1)=(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) : ℤ) := by
    simpa [_root_.ThreeSum1960614.Machine.ThreeSum.SourceControlLayout.values,base,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.controls,cover,p,xs]
      using sources.controls.getD (i := 1) (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.SourceControlLayout.values]) 0
  have hbankEq : bank=occ+_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))*
      _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) := rfl
  have hHeader := _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorWantedHeader.meets (d := d+1) (μ := μ₂)
    (by rfl : program[253]?=some LightEncodedColorWantedHeader.body) hw (by change wanted ≤ lim.space; omega) cover₂
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hHeader _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hHeader ?_ ?_ ?_ ?_
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
     on_goal -1 => (rintro out μ₃ ⟨hout, hmem⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₃
  have hout' : out=(wanted : ℤ) := hout
  have wanted2 : ((wanted : ℤ)+2).toNat=wanted+2 := by omega
  have base1 : ((base : ℤ)+1).toNat=base+1 := by omega
  have base8 : ((base : ℤ)+8).toNat=base+8 := by omega
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (base : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hout', wanted2, hnext]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hout', wanted2, hnext] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hout', wanted2, hnext] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (occ : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, base8, readOcc]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [base8, readOcc] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, base8, readOcc] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, base1, readS]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [base1, readS] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, base1, readS] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (bank : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbankEq]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hbankEq] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbankEq] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hResult := _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorResult.meets (d := d+1) (μ := μ₂)
    (prime := _root_.ThreeSum.EncodedColorLayout.prime free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) (cover := cover) (wanted := wanted) (controls := base) (bank := bank)
    (out := finish) (len := xs.length) (p := p)
    (by rfl : program[254]?=some LightEncodedColorResult.body) hw (by omega) (by omega) (by omega)
    (by omega) (by omega) hfinishSpace hlenWord hpWord
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hResult _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hResult ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hptr, hout', hlast]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hptr, hout', hlast] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hptr, hout', hlast] <;> omega)
     on_goal -1 => (rintro r ν ⟨hr, finalHeads, keptResult⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have primes₂ := primes.of_kept keptSources le_rfl
  have heads₂ := heads.of_kept keptSources (by simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using hfree)
  have count₂ : μ₂ (_root_.ThreeSum.EncodedColorLayout.normalizedEnd free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n))=(xs.length : ℤ) :=
    (keptSources _ (by unfold _root_.ThreeSum.EncodedColorLayout.prime at hmeta; omega)).trans hcount
  have hkeyEnd : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd cover (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) ≤ finish := by
    have hh : wanted=_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData.keyEnd cover (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))+3*xs.length := rfl
    omega
  refine ⟨⟨A,hsA,B,hsB,C,hsC,hr,⟨finalHeads,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩,?_⟩
  · exact heads₂.of_kept keptResult (by simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using (show free+8 ≤ finish by omega))
  · exact (keptResult _ (by unfold _root_.ThreeSum.EncodedColorLayout.prime at hmeta; omega)).trans count₂
  · exact normalized₂.keep keptResult ha hb hc (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
      (by change _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) ≤ finish; omega)
  · exact primes₂.of_kept keptResult (by change cover ≤ finish; omega)
  · exact cover₂.of_kept (fun i hi => keptResult i (hi.trans_le hkeyEnd))
  · exact _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedData.of_kept wanted₂ keptResult (by change base ≤ finish; omega)
  · simpa only [hlast,base,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.controls,cover,p,xs,finish,
      _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish] using sources.of_kept keptResult le_rfl
  · dsimp only
    rw [keptResult _ (by change wanted < finish; omega)]
    exact countBound
  · apply lifts.of_kept keptResult
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists.keys_length]
    change wanted ≤ finish
    omega
  · intro i hi
    exact (keptResult i (by omega)).trans ((keptSources i (by omega)).trans (keptPrime i hi))
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.program_meets__implementation_972ef60e93) := (@ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.program_meets__implementation_972ef60e93)

#print axioms solution
