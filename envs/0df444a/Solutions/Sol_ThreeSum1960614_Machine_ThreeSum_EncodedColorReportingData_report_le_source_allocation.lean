-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingData.report_le_source_allocation
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:05:01.281763+00:00
-- url     : https://prove2.me/submissions/481e0981-f687-416f-b7f6-3cb281cb72a2

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorResources_pipeline_space_bound
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SourceBandBanksCosts_span_count_le_encoderCount
import Theorems.Thm_ThreeSum_Histograms_correlation_histograms
import Theorems.Thm_ThreeSum_LightMinimum_least_value_le
import Theorems.Thm_ThreeSum_LocalCoverBounds_pow_le_choose_mul

local instance platformRadixNonzero_48e77ea97f (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
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
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BandScales
end ThreeSum.BandScales
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
namespace ThreeSum.EncodedColorReportingData
end ThreeSum.EncodedColorReportingData
namespace ThreeSum.EncodedColorStageCosts
end ThreeSum.EncodedColorStageCosts
namespace ThreeSum.EncodedColorWantedCosts
end ThreeSum.EncodedColorWantedCosts
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
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightCoverKeyData
end ThreeSum.LightCoverKeyData
namespace ThreeSum.LightGuardedWanted
end ThreeSum.LightGuardedWanted
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba
namespace ThreeSum.LightOriginalOffset
end ThreeSum.LightOriginalOffset
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
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
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.SourceControlCosts
end ThreeSum.SourceControlCosts
namespace ThreeSum.SourceFiniteCosts
end ThreeSum.SourceFiniteCosts
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.ThreeSumColorBudgets
end ThreeSum.ThreeSumColorBudgets
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
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
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
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts
end ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts
end ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts
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
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightClassFilter
end ThreeSum1960614.Machine.ThreeSum.LightClassFilter
namespace ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData
end ThreeSum1960614.Machine.ThreeSum.LightCoverKeyData
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
namespace ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset
end ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset
namespace ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
end ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
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
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.ThreeSum.SourceControlCosts
end ThreeSum1960614.Machine.ThreeSum.SourceControlCosts
namespace ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts
end ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.Switch
end ThreeSum1960614.Machine.ThreeSum.Switch
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets
end ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
end ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales
namespace ThreeSum1960614.Machine.ThreeSum.WantedPairs
end ThreeSum1960614.Machine.ThreeSum.WantedPairs
namespace ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys
end ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys

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











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







end ThreeSum.LightClassFilter

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























end ThreeSum.BandRawA

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

































theorem residue_eq_iff {M : ℕ} (hM : 0 < M) (a b d : ℤ) :
    _root_.ThreeSum.LightResidues.residue M 1 b=_root_.ThreeSum.LightResidues.residue M 1 (a+d) ↔ (M : ℤ) ∣ a+d-b := by
  rw [← Nat.cast_inj (R := ℤ),_root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_cast hM,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_cast hM,one_mul,one_mul]
  exact Int.modEq_iff_dvd







end ThreeSum.WantedPairs

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



end ThreeSum.LightBalancedWanted

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















end ThreeSum.EncodedColorPrimeCosts

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





end ThreeSum.EncodedColorNormalizedData

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

/-! # Numeric envelopes for the actually balanced wanted records -/

namespace ThreeSum.EncodedColorWantedCosts
open _root_.ThreeSum.EncodedColorWantedCosts


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.WantedResidueKeys
open _root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys

set_option maxHeartbeats 1800000









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





theorem sourceBase_mono {free M h J len len' : ℕ} (hlen : len ≤ len') :
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.sourceBase free M h J len ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.sourceBase free M h J len' := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.sourceBase_eq,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.sourceBase_eq]
  gcongr







end ThreeSum.EncodedColorWantedCosts

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

















open _root_.Filter



end ThreeSum.ThreeSumColorBudgets

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



















theorem base_le {free n p M len : ℕ} [NeZero M] {xs : List ℤ} (hlen : xs.length ≤ len) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorFiniteSources.base free n p M xs ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.sourceBase free n M len :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.sourceBase_le free p M (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n))
    (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) xs).trans (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.sourceBase_mono hlen)









theorem finish_le {base bound NL NR n : ℕ} (hn : 0 < n)
    (hb : base ≤ bound) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceControlsHost.finish base NL NR (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
      (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.finish bound n := by
  apply (_root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.finish_le hn hNL hNR).trans
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.finish
  omega



end ThreeSum.EncodedColorStageCosts

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingData

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
open _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
section

theorem ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingData.report_le_source_allocation__implementation_6199a9e04d {μ : ℕ → ℤ} {free n : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : 0 < n) (U : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC ≤ free+(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.need n U).cells := by
  obtain ⟨ha,hb,hc⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.normalized_lengths H
  have hlen := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences_length_le
    (hsA := hsA) (hsB := hsB) (hsC := hsC) ha hb hc
  have hbase : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.controls free n A B C hsA hsB hsC ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.sourceBound free n := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.base_le hlen
  have hfinish : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.finish free n A B C hsA hsB hsC ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.finishBound free n := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.finish_le hn hbase hb hc
  have hs : _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.finishBound free n+8 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPipeline.space free n U :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hall := (Nat.add_le_add_right hfinish 8).trans (hs.trans (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.pipeline_space_bound free n U))
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.reportBase,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.need,Nat.add_assoc] using hall
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingData.report_le_source_allocation__implementation_6199a9e04d) := (@ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingData.report_le_source_allocation__implementation_6199a9e04d)

#print axioms solution
