-- Prove2me | solution 1 for ThreeSum1960614.costs_solve_3sum
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T10:16:17.076681+00:00
-- url     : https://prove2.me/submissions/a152b47d-9de7-4972-a85c-2b14e6774861

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Ceil
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
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
import Mathlib.Algebra.Order.Floor.Semiring
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
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Field.Basic
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
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
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
import Mathlib.Order.Filter.AtTopBot.Basic
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Wrap_realized
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSumApsp_FromClaims_solvedAt_of_realized
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSumApsp_WordRam_bigO_of_le_rpow
import Theorems.Thm_ThreeSum_ArithmeticStageBounds_powerBound_of_fifth
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BandPrimeCosts_setup_time_le_budget
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BandPrimeCosts_timeBudget_powerBound
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BandScales_bandDivisor_log_rate
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BandScales_bandRoot_log_rate
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BandScales_bandSize_log_rate
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_CostLedger_prefixBoxes_log_bound
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorResources_dimensions
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_HierarchyScales_bandCount_log_rate
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_HierarchyScales_hierarchyEnvelope_log_rate
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_HierarchyScales_initial_query_eventually_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverCost_build_time_bound
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverMagnitude_bounds
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightThreeSumHybrid_solves
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LocalParameterBounds_time_bound
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_MassScales_falseNumerator_log_rate
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_Scales_typedOutputs_log_ratio_tendsto
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_components
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingCosts_overhead_powerBound
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_add_same
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_StageBounds_terminalChoices_log_rate
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_ThreeSumFastResourcesHybrid_poly_need
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_TrimScales_fullOutputs_log_rate
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_TrimScales_localLength_log_rate
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_TrimScales_replicatedHalf_log_rate
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_TrimScales_representationBound_log_rate
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_UniformStageBounds_budget_active_powerBound
import Theorems.Thm_ThreeSum_BandPrimeCosts_aggregate_time_le
import Theorems.Thm_ThreeSum_LightOriginalOffset_time_bound
import Theorems.Thm_ThreeSum_LightRadixKeys_time_bound
import Theorems.Thm_ThreeSum_ModuloCosts_roundedPower_fifth
import Theorems.Thm_ThreeSum_ModuloCosts_time_bound
import Theorems.Thm_ThreeSum_Scales_natSqrt_ratio_tendsto_zero
import Theorems.Thm_ThreeSum_SubsetAddress_enumerationWork_bound

private theorem ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.add_same {f g : ℕ → ℕ} {a : ℝ}
    (hf : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a)
    (hg : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound g a) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => f n+g n) a := by
  exact _root_.ThreeSum.StageBounds.PowerBound.add_same hf hg


local instance platformRadixNonzero_8b0967f0b1 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Filter
end Filter
namespace Finset
end Finset
namespace Light
end Light
namespace Light.Logs
end Light.Logs
namespace Light.Sec3
end Light.Sec3
namespace Polynomial
end Polynomial
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
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandPrimeCosts
end ThreeSum.BandPrimeCosts
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockSourceSharing
end ThreeSum.BlockSourceSharing
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.EncodedColorPrimeCosts
end ThreeSum.EncodedColorPrimeCosts
namespace ThreeSum.EncodedColorReportingCosts
end ThreeSum.EncodedColorReportingCosts
namespace ThreeSum.EncodedColorResources
end ThreeSum.EncodedColorResources
namespace ThreeSum.EncodedColorSourcesCosts
end ThreeSum.EncodedColorSourcesCosts
namespace ThreeSum.EncodedColorTime
end ThreeSum.EncodedColorTime
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.HierarchyScales
end ThreeSum.HierarchyScales
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightBandRawAColor
end ThreeSum.LightBandRawAColor
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightColorArray
end ThreeSum.LightColorArray
namespace ThreeSum.LightColorBands
end ThreeSum.LightColorBands
namespace ThreeSum.LightColorClasses
end ThreeSum.LightColorClasses
namespace ThreeSum.LightColorParametersCosts
end ThreeSum.LightColorParametersCosts
namespace ThreeSum.LightColorScanCosts
end ThreeSum.LightColorScanCosts
namespace ThreeSum.LightDenseSetupCosts
end ThreeSum.LightDenseSetupCosts
namespace ThreeSum.LightGlobalKeys
end ThreeSum.LightGlobalKeys
namespace ThreeSum.LightGlobalSizes
end ThreeSum.LightGlobalSizes
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba
namespace ThreeSum.LightLocalCoverInitResources
end ThreeSum.LightLocalCoverInitResources
namespace ThreeSum.LightLocalCoverMagnitude
end ThreeSum.LightLocalCoverMagnitude
namespace ThreeSum.LightLocalCoverResources
end ThreeSum.LightLocalCoverResources
namespace ThreeSum.LightLocalKeyRow
end ThreeSum.LightLocalKeyRow
namespace ThreeSum.LightLocalKeys
end ThreeSum.LightLocalKeys
namespace ThreeSum.LightMaskHashes
end ThreeSum.LightMaskHashes
namespace ThreeSum.LightModuloCounts
end ThreeSum.LightModuloCounts
namespace ThreeSum.LightRawAKeys
end ThreeSum.LightRawAKeys
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightScales
end ThreeSum.LightScales
namespace ThreeSum.LightSmallDivide
end ThreeSum.LightSmallDivide
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightSubsetEnumeration
end ThreeSum.LightSubsetEnumeration
namespace ThreeSum.LightSubsetEnumerationSetup
end ThreeSum.LightSubsetEnumerationSetup
namespace ThreeSum.LightSwitchCosts
end ThreeSum.LightSwitchCosts
namespace ThreeSum.LightThreeSumHybrid
end ThreeSum.LightThreeSumHybrid
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.MassScales
end ThreeSum.MassScales
namespace ThreeSum.ModuloCosts
end ThreeSum.ModuloCosts
namespace ThreeSum.ModuloRuntime
end ThreeSum.ModuloRuntime
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.RawAKeyLists
end ThreeSum.RawAKeyLists
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankCosts
end ThreeSum.SharedReportingBankCosts
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.SharedReportingCosts
end ThreeSum.SharedReportingCosts
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts
namespace ThreeSum.SourceBandCosts
end ThreeSum.SourceBandCosts
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.StageBounds.PowerBound
end ThreeSum.StageBounds.PowerBound
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.Switch
end ThreeSum.Switch
namespace ThreeSum.ThreeSumColorBudgets
end ThreeSum.ThreeSumColorBudgets
namespace ThreeSum.ThreeSumColorDriverCosts
end ThreeSum.ThreeSumColorDriverCosts
namespace ThreeSum.ThreeSumHybridCosts
end ThreeSum.ThreeSumHybridCosts
namespace ThreeSum.ThreeSumHybridEndBridge
end ThreeSum.ThreeSumHybridEndBridge
namespace ThreeSum.ThreeSumParameterResources
end ThreeSum.ThreeSumParameterResources
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales
namespace ThreeSum.UniformStageBounds
end ThreeSum.UniformStageBounds
namespace ThreeSum1960614
end ThreeSum1960614
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Logs
end ThreeSum1960614.Machine.Light.Logs
namespace ThreeSum1960614.Machine.Light.Sec3
end ThreeSum1960614.Machine.Light.Sec3
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
end ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts
end ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts
namespace ThreeSum1960614.Machine.ThreeSum.BandRawA
end ThreeSum1960614.Machine.ThreeSum.BandRawA
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
end ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
namespace ThreeSum1960614.Machine.ThreeSum.ColorClassLists
end ThreeSum1960614.Machine.ThreeSum.ColorClassLists
namespace ThreeSum1960614.Machine.ThreeSum.ColorParameters
end ThreeSum1960614.Machine.ThreeSum.ColorParameters
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts
end ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingCosts
end ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingCosts
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
end ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorSourcesCosts
end ThreeSum1960614.Machine.ThreeSum.EncodedColorSourcesCosts
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorTime
end ThreeSum1960614.Machine.ThreeSum.EncodedColorTime
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.HierarchyScales
end ThreeSum1960614.Machine.ThreeSum.HierarchyScales
namespace ThreeSum1960614.Machine.ThreeSum.Karatsuba
end ThreeSum1960614.Machine.ThreeSum.Karatsuba
namespace ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
end ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
namespace ThreeSum1960614.Machine.ThreeSum.LightBandRawAColor
end ThreeSum1960614.Machine.ThreeSum.LightBandRawAColor
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightColorArray
end ThreeSum1960614.Machine.ThreeSum.LightColorArray
namespace ThreeSum1960614.Machine.ThreeSum.LightColorBands
end ThreeSum1960614.Machine.ThreeSum.LightColorBands
namespace ThreeSum1960614.Machine.ThreeSum.LightColorClasses
end ThreeSum1960614.Machine.ThreeSum.LightColorClasses
namespace ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts
end ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts
namespace ThreeSum1960614.Machine.ThreeSum.LightColorScanCosts
end ThreeSum1960614.Machine.ThreeSum.LightColorScanCosts
namespace ThreeSum1960614.Machine.ThreeSum.LightDenseSetupCosts
end ThreeSum1960614.Machine.ThreeSum.LightDenseSetupCosts
namespace ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys
end ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys
namespace ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes
end ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes
namespace ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
end ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInitResources
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInitResources
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverResources
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverResources
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalKeyRow
end ThreeSum1960614.Machine.ThreeSum.LightLocalKeyRow
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalKeys
end ThreeSum1960614.Machine.ThreeSum.LightLocalKeys
namespace ThreeSum1960614.Machine.ThreeSum.LightMaskHashes
end ThreeSum1960614.Machine.ThreeSum.LightMaskHashes
namespace ThreeSum1960614.Machine.ThreeSum.LightModuloCounts
end ThreeSum1960614.Machine.ThreeSum.LightModuloCounts
namespace ThreeSum1960614.Machine.ThreeSum.LightRawAKeys
end ThreeSum1960614.Machine.ThreeSum.LightRawAKeys
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightScales
end ThreeSum1960614.Machine.ThreeSum.LightScales
namespace ThreeSum1960614.Machine.ThreeSum.LightSmallDivide
end ThreeSum1960614.Machine.ThreeSum.LightSmallDivide
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup
end ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup
namespace ThreeSum1960614.Machine.ThreeSum.LightSwitchCosts
end ThreeSum1960614.Machine.ThreeSum.LightSwitchCosts
namespace ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybrid
end ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybrid
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.MassScales
end ThreeSum1960614.Machine.ThreeSum.MassScales
namespace ThreeSum1960614.Machine.ThreeSum.ModuloCosts
end ThreeSum1960614.Machine.ThreeSum.ModuloCosts
namespace ThreeSum1960614.Machine.ThreeSum.ModuloRuntime
end ThreeSum1960614.Machine.ThreeSum.ModuloRuntime
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.RawAKeyLists
end ThreeSum1960614.Machine.ThreeSum.RawAKeyLists
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts
end ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts
namespace ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
end ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandCosts
end ThreeSum1960614.Machine.ThreeSum.SourceBandCosts
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound
end ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.Switch
end ThreeSum1960614.Machine.ThreeSum.Switch
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets
end ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverCosts
end ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverCosts
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts
end ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridEndBridge
end ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridEndBridge
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources
end ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales
namespace ThreeSum1960614.Machine.ThreeSum.UniformStageBounds
end ThreeSum1960614.Machine.ThreeSum.UniformStageBounds
namespace ThreeSum1960614.Machine.ThreeSum1960614
end ThreeSum1960614.Machine.ThreeSum1960614
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSum1960614.Machine.ThreeSumApsp.Spec
end ThreeSum1960614.Machine.ThreeSumApsp.Spec
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

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
# Building the color of every original array position

The program constructs its own binary-power table and evaluates one selected
two-coordinate coloring on every index. No index-bit or coloring oracle is
part of the input. Memory outside the output colors and scratch is preserved.
-/

namespace ThreeSum.LightColorArray
open _root_.ThreeSum.LightColorArray


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

set_option maxHeartbeats 1200000







variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem time_bound (W n : ℕ) : _root_.ThreeSum.LightColorArray.time W n ≤ 600*(W+1)*(n+1) := by
  unfold _root_.ThreeSum.LightColorArray.time _root_.Light.powTableTime _root_.ThreeSum.LightColorIndex.time _root_.ThreeSum.LightMaskErase.time
  nlinarith

end ThreeSum.LightColorArray

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Evaluating a whole list of one-hot mask hashes

This wrapper builds the powers table itself, hashes each stored mask, and
writes the raw nonnegative values. It is shared by the local-cover matrix
construction and input-source encoding. The cost is linear in the number
of masks times their width; no evaluation oracle is assumed.
-/

namespace ThreeSum.LightMaskHashes
open _root_.ThreeSum.LightMaskHashes


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

set_option maxHeartbeats 1000000









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem time_bound (L n : ℕ) : _root_.ThreeSum.LightMaskHashes.time L n ≤ 300*(L+1)*(n+1) := by
  unfold _root_.ThreeSum.LightMaskHashes.time _root_.Light.powTableTime _root_.ThreeSum.LightOneHot.time
  nlinarith

end ThreeSum.LightMaskHashes

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Output-sensitive subset-layer enumeration in the benchmark language

The recursive routine writes into consecutive output cells. Empty layers
return immediately; a zero-cardinality layer emits one mask. The two
recursive children share the output buffer and write adjacent, disjoint
segments. No ambient Boolean cube is scanned and no output list is copied.
-/

namespace ThreeSum.LightSubsetEnumeration
open _root_.ThreeSum.LightSubsetEnumeration


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

















theorem time_bound (L k : ℕ) :
    _root_.ThreeSum.LightSubsetEnumeration.time L k ≤ 150*((4*L+1)*L.choose k+1) := by
  exact Nat.mul_le_mul_left 150 (_root_.ThreeSum.SubsetAddress.enumerationWork_bound L k)







end ThreeSum.LightSubsetEnumeration

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
Expansion-232 analytic interface for the actual machine-source modules.
The definition bodies use the audited rational quartic parameter choice.
Closed analytic proofs supply the bounds; no program correctness contract
is assumed by this interface. Additional operational exponents must remain
the individual raw ledger costs for the universal rational-r bridge.
-/

noncomputable section
namespace ThreeSum.Parameters
open _root_.ThreeSum.Parameters

open _root_.Set
































theorem actual_costLedger_eq :
    _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.costLedger _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa (_root_.ThreeSum.Parameters.entropy _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta) = _root_.ThreeSum1960614.costs := by
  norm_num [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.costLedger,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa,_root_.ThreeSum.Parameters.entropy,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction,
    _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta,_root_.ThreeSum1960614.costs,_root_.ThreeSum1960614.ledger,
    _root_.ThreeSum1960614.E,_root_.ThreeSum1960614.kappa,_root_.ThreeSum1960614.entropy,
    _root_.ThreeSum1960614.epsilon,_root_.ThreeSum1960614.beta,_root_.ThreeSum1960614.saving,
    _root_.ThreeSum1960614.tau,_root_.ThreeSum1960614.rho,_root_.ThreeSum1960614.theta]

































end ThreeSum.Parameters

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Logarithms, the cube root and halves, without division

Four routines on local variables only; none of them touches the memory.

* log2(x) returns ⌊log₂ x⌋ (0 for x = 0) by doubling (`log2_meets`).
* clog2(x) returns ⌈log₂ x⌉ (0 for x ≤ 1) by doubling (`clog2_meets`).
* cbrtCeil(n) returns the least s with s³ ≥ n, which is ⌈n^{1/3}⌉, by counting up
  (`cbrtCeil_meets`).
* half(h) returns ⌈h/2⌉ by counting up (`half_meets`).

Each of them is one loop that tries the candidates 0, 1, 2, … in turn.  Local variable 0 holds the
argument and receives the result, local variable 1 holds the candidate (`Arg`, `Cand`), and the two
logarithms keep a power of two in local variable 2 (`Power`).
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

namespace Logs
open _root_.Light.Logs






end Logs

open _root_.Light.Logs
open _root_.ThreeSum1960614.Machine.Light.Logs

/-! ## The logarithm, rounded down -/







/-! ## The logarithm, rounded up -/







/-! ## The cube root, rounded up -/









theorem cbrtLeast_le {n s : ℕ} (h : n ≤ s ^ 3) : _root_.Light.cbrtLeast n ≤ s :=
  Nat.find_min' (_root_.Light.exists_le_cube n) h

theorem cbrtLeast_le_self (n : ℕ) : _root_.Light.cbrtLeast n ≤ n :=
  _root_.ThreeSum1960614.Machine.Light.cbrtLeast_le (Nat.le_self_pow (by norm_num) n)













/-! ## Halves, rounded up -/







end Light

end

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



/-! ## Tasks and solvers -/















theorem le_timeUpTo (Tn : ℕ → ℕ → ℕ) (n : ℕ) {U : ℕ} {u : ℝ} (hu : (U : ℝ) ≤ u) :
    (Tn n U : ℝ) ≤ _root_.Light.timeUpTo Tn n u :=
  Nat.cast_le.2 (Finset.le_sup (f := Tn n)
    (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hu))))

/-- What bounds the time for every natural number `U ≤ u` bounds `timeUpTo`.  For a negative `u`
there is still `U = 0`. -/
theorem timeUpTo_le {Tn : ℕ → ℕ → ℕ} {n : ℕ} {u B : ℝ}
    (h : ∀ U : ℕ, (U : ℝ) ≤ max u 0 → (Tn n U : ℝ) ≤ B) : _root_.Light.timeUpTo Tn n u ≤ B := by
  obtain ⟨U, hU, hsup⟩ := Finset.exists_mem_eq_sup (Finset.range (⌊u⌋₊ + 1))
    ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ (Tn n)
  rw [_root_.Light.timeUpTo, hsup]
  refine h U ((Nat.cast_le.2 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hU))).trans ?_)
  rcases le_total 0 u with hu | hu
  · exact (Nat.floor_le hu).trans (le_max_left u 0)
  · rw [Nat.floor_of_nonpos hu, Nat.cast_zero]
    exact le_max_right u 0

/-- A solver with a polynomially bounded need solves its task in its own time. -/
theorem Solves.solvedIn {task : _root_.Light.Task} {P : _root_.ThreeSum1960614.Machine.Light.Program} {p : ℕ} {Tn : ℕ → ℕ → ℕ} {need : ℕ → ℕ → _root_.ThreeSum1960614.Machine.Light.Need}
    (hs : _root_.ThreeSum1960614.Machine.Light.Solves task P p Tn need) (hp : _root_.ThreeSum1960614.Machine.Light.PolyNeed need) : _root_.ThreeSum1960614.Machine.Light.SolvedIn task (_root_.Light.timeUpTo Tn) :=
  ⟨P, p, Tn, need, hp, hs, fun n _ _ _ _ hu => _root_.ThreeSum1960614.Machine.Light.le_timeUpTo Tn n hu⟩

/-! ## Hosts -/





/-! ## Tasks with a list of parameters -/











end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Running the word RAM: words, steps, pieces of code, straight-line code, branches

What the proofs about compiled code need to know about the word RAM in which the paper's claims are
stated.

* **Words.**  `wd W v` is the word of the integer v.  If v is in the range of signed words
  (`InRange`), the word gives back v (`toInt_wd`).
* **Steps.**  The end statement defines only whole runs (`exec`).  A configuration (`Cfg`) and a
  single step (`step`) are defined here; `exec_succ_of_step` and `exec_succ_of_verdict` say that
  `exec` takes one step at a time.
* **Runs.**  `Steps P n c c'`: exactly n steps lead from c to c', none of them a verdict.
  Runs are composed by `Steps.trans`; a run that ends before a verdict gives the value of `exec`
  (`exec_of_steps`), and more time does not change that value (`exec_mono`).
* **Code.**  `CodeAt P pos l`: the program P has the instructions of the list l from position pos
  on.
* **Straight-line code.**  Six instructions only change the memory (`Straight`, `effect`); a list
  of them runs through in its length (`steps_straight`).
* **Known numbers.**  On cells that hold the words of known numbers, an instruction writes the word
  of a known number: `effect_add`, …, `effect_store` for the memory; `steps_add`, `steps_sub`,
  `steps_load`, `steps_store` for the step.
* **Branches and verdicts.**  A branch on a cell that holds a known number is `steps_bltz`;
  `Steps.branch` turns its two outcomes into the two outcomes of a test.  The verdicts are
  `step_accept` and `step_reject`.
* **Framing.**  `AgreeOutside s m m'`: the memories m and m' are equal outside the set s of cells.
  For code without stores such a set can be read off the text (`WritesIn`, `agreeOutside_effects`).
-/

@[expose] public section

namespace ThreeSumApsp.WordRam
open _root_.ThreeSumApsp.WordRam


open _root_.EndStatement renaming Instr -> Instr
open _root_.EndStatement renaming exec -> exec
open _root_.EndStatement renaming loadWords -> loadWords

variable {W : ℕ} {P : List _root_.EndStatement.Instr}

/-! ## Words -/























/-! ## Configurations and single steps -/





/-! ## Runs -/













/-- Within no steps there is no verdict. -/
theorem exec_zero (c : _root_.ThreeSumApsp.WordRam.Cfg W) : _root_.EndStatement.exec P 0 c.pc c.mem = none := by rw [_root_.EndStatement.exec]

section

private theorem private_c654e189a0_exec_succ (t : ℕ) (c : _root_.ThreeSumApsp.WordRam.Cfg W) : _root_.EndStatement.exec P (t + 1) c.pc c.mem =
    match _root_.ThreeSumApsp.WordRam.step P c with
    | .inr verdict => some (verdict, c.mem)
    | .inl next => _root_.EndStatement.exec P t next.pc next.mem := by
  rw [_root_.EndStatement.exec, _root_.ThreeSumApsp.WordRam.step]
  cases P.getD c.pc _root_.EndStatement.Instr.reject <;> rfl
end


/-- A step that gives a verdict ends the run. -/
theorem exec_succ_of_verdict {c : _root_.ThreeSumApsp.WordRam.Cfg W} {v : Bool} (h : _root_.ThreeSumApsp.WordRam.step P c = .inr v) (t : ℕ) :
    _root_.EndStatement.exec P (t + 1) c.pc c.mem = some (v, c.mem) := by rw [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_c654e189a0_exec_succ, h]

/-- After a step that gives no verdict the run goes on, with one step less. -/
theorem exec_succ_of_step {c c' : _root_.ThreeSumApsp.WordRam.Cfg W} (h : _root_.ThreeSumApsp.WordRam.step P c = .inl c') (t : ℕ) :
    _root_.EndStatement.exec P (t + 1) c.pc c.mem = _root_.EndStatement.exec P t c'.pc c'.mem := by rw [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.private_c654e189a0_exec_succ, h]



/-- More time does not change the outcome of a run. -/
theorem exec_mono {t t' : ℕ} {c : _root_.ThreeSumApsp.WordRam.Cfg W} {r : Bool × (ℤ → BitVec W)}
    (h : _root_.EndStatement.exec P t c.pc c.mem = some r) (ht : t ≤ t') : _root_.EndStatement.exec P t' c.pc c.mem = some r := by
  induction t generalizing c t' with
  | zero => simp [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.exec_zero] at h
  | succ t ih =>
    obtain ⟨t'', rfl⟩ : ∃ t'', t' = t'' + 1 := ⟨t' - 1, by omega⟩
    cases hs : _root_.ThreeSumApsp.WordRam.step P c with
    | inr v => rwa [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.exec_succ_of_verdict hs] at h ⊢
    | inl n =>
      rw [_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.exec_succ_of_step hs] at h ⊢
      exact ih h (by omega)

/-! ## Pieces of code -/















/-! ## Straight-line code -/



















/-! ## Single instructions on cells that hold known numbers -/

section known

variable {m : ℤ → BitVec W} {i j k a b : ℤ}





















end known

/-! ## Branches and verdicts -/









/-! ## Framing -/

section framing

variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}

























end framing

end ThreeSumApsp.WordRam

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-array construction of all three color classes

A fixed six-procedure program builds the color array and extracts three
disjoint output segments with length headers. The third class is negated.
Original values and their multiplicities are kept until class normalization.
-/

namespace ThreeSum.LightColorClasses
open _root_.ThreeSum.LightColorClasses


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









theorem time_bound (W n : ℕ) : _root_.ThreeSum.LightColorClasses.time W n ≤ 1200*(W+1)*(n+1) := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.LightColorArray.time_bound W n
  unfold _root_.ThreeSum.LightColorClasses.time _root_.ThreeSum.LightClassFilter.time
  nlinarith

end ThreeSum.LightColorClasses

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Karatsuba as a fixed program in the benchmark language

The procedure below is a finite `Light.Stmt`, independent of the input
capacity. Recursive products share an eight-capacity scratch area. The
linear-time `half` routine avoids an additional persistent power table.
-/

namespace ThreeSum.LightKaratsuba
open _root_.ThreeSum.LightKaratsuba


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba
open _root_.Polynomial





















theorem time_bound (k : ℕ) : _root_.ThreeSum.LightKaratsuba.time k + 2500 * 2 ^ k ≤ 2530 * 3 ^ k := by
  induction k with
  | zero => norm_num [_root_.ThreeSum.LightKaratsuba.time]
  | succ k ih =>
    simp only [_root_.ThreeSum.LightKaratsuba.time, pow_succ]
    nlinarith

theorem time_le (k : ℕ) : _root_.ThreeSum.LightKaratsuba.time k ≤ 2530 * 3 ^ k :=
  (Nat.le_add_right _ _).trans (_root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.time_bound k)



















section Join

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d pLinear pFill : ℕ}



end Join

section BaseCase

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end BaseCase





















section RecursiveExecution

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {pSelf pHalf pLinear pFill : ℕ}



end RecursiveExecution

section CompleteProcedure

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {pSelf pHalf pLinear pFill : ℕ}









end CompleteProcedure

end ThreeSum.LightKaratsuba

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Computing one complete row of signed local output keys

For every stored output mask, this fixed program sums the true and false
coefficients outside that mask and subtracts the two sums. It constructs
its own zero row and powers table. Both input coefficient rows and the
literal output-mask enumeration remain intact.
-/

namespace ThreeSum.LightLocalKeyRow
open _root_.ThreeSum.LightLocalKeyRow


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem time_bound (L n : ℕ) : _root_.ThreeSum.LightLocalKeyRow.time L n ≤ 950*(L+1)*(n+1) := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskHashes.time_bound L n
  unfold _root_.ThreeSum.LightLocalKeyRow.time _root_.Light.fillTime _root_.ThreeSum.LightArray.linearTime
  nlinarith

end ThreeSum.LightLocalKeyRow

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact natural quotient by a small counting loop

This helper is used for size parameters whose numerator is logarithmic in
the original input length. Its time is linear in the quotient, explicitly
charged below. A zero divisor returns zero, matching natural division.
-/

namespace ThreeSum.LightSmallDivide
open _root_.ThreeSum.LightSmallDivide


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}











theorem time_bound (a b : ℕ) : _root_.ThreeSum.LightSmallDivide.time a b ≤ 20*a+40 := by
  have h := Nat.div_le_self a b
  unfold _root_.ThreeSum.LightSmallDivide.time
  omega

end ThreeSum.LightSmallDivide

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A fixed subset-layer enumerator with its own power-table construction

The main theorem has no supplied lookup-table correctness assumption. The
only auxiliary memory is a table of `L+1` powers of two, built once before
the recursive enumeration. The output has exactly `L.choose k` cells.
-/

namespace ThreeSum.LightSubsetEnumerationSetup
open _root_.ThreeSum.LightSubsetEnumerationSetup


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}











theorem time_bound (L k : ℕ) : _root_.ThreeSum.LightSubsetEnumerationSetup.time L k ≤ 800*(L+1)*(L.choose k+1) := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.time_bound L k
  unfold _root_.ThreeSum.LightSubsetEnumerationSetup.time _root_.Light.powTableTime
  nlinarith

end ThreeSum.LightSubsetEnumerationSetup

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
The actual finite maximum of the twelve operational charges. Using this
exponent in the complete runtime assembly retains every strict target
above the maximum, including targets below the convenient principal cap.
-/

noncomputable section
namespace ThreeSum.Parameters
open _root_.ThreeSum.Parameters




theorem fold_max_upper (charges : List ℝ) :
    ∀ t ∈ charges, t ≤ charges.foldr max 0 := by
  induction charges with
  | nil => simp
  | cons x xs ih =>
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact le_max_left _ _
      · exact (ih t ht).trans (le_max_right _ _)

theorem fold_max_lt (charges : List ℝ) {r : ℝ} (hr : 0 < r)
    (hcharges : ∀ t ∈ charges, t < r) : charges.foldr max 0 < r := by
  induction charges with
  | nil => exact hr
  | cons x xs ih =>
      exact max_lt (hcharges x (by simp))
        (ih (fun t ht => hcharges t (by simp [ht])))

theorem all_costs_le_raw_exponent :
    ∀ t ∈ _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.costLedger _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa (_root_.ThreeSum.Parameters.entropy _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta), t ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent :=
  _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.fold_max_upper _

theorem raw_exponent_lt_of_costs_lt {r : ℝ} (hr : 0 < r)
    (hcost : ∀ t ∈ _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.costLedger _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa (_root_.ThreeSum.Parameters.entropy _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta), t < r) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent < r := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.fold_max_lt _ hr hcost





theorem raw_exponent_lower : (193/100 : ℝ) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent := by
  have hb : 2-_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent :=
    _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.all_costs_le_raw_exponent _ (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.costLedger])
  exact (by norm_num [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving] : (193/100 : ℝ) ≤ 2-epsilon*boxSaving).trans hb

theorem raw_exponent_nonnegative : (0 : ℝ) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent := by
  linarith [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.raw_exponent_lower]

end ThreeSum.Parameters

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# 3SUM: from a solver of the task to a program for the layout of the end statement

3SUM (Theorem 22).  `realized_threeSum`: if the task `s3Task` is solved in time T, then
`EndStatement.ThreeSum` is solved on the word RAM within a constant times T.

The input is n in cell 0 and the n numbers in the cells 1, …, n; the free pointer is n + 1
(`threeSumInst`).  The task speaks of the vector that is read from the list of the numbers, which is
the vector of the instance (`vecOf_ofFn`).  So the input meets the task's precondition
(`pre_threeSum`), and the result of a solver is the right verdict (`post_threeSum`).
-/

@[expose] public section

namespace Light.Sec3
open _root_.Light.Sec3


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp
open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam
open _root_.ThreeSumApsp.Spec
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.Spec











/-- **3SUM**: if the task is solved in time T, then 3SUM is solved on the word RAM within a constant
times T. -/
theorem realized_threeSum (T : ℕ → ℝ → ℝ) (h : _root_.ThreeSum1960614.Machine.Light.SolvedIn _root_.ThreeSum1960614.Machine.Light.s3Task T) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Realized _root_.EndStatement.ThreeSum T :=
  _root_.ThreeSum1960614.Machine.Light.Sec3.wrap3Sum.realized h

end Light.Sec3

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# From a real exponent to a rational one

An item statement bounds the steps of a program by `C (n^a + 1)`, with real numbers `C` and `a`.
The end statement uses Lean's core library only.  It asks for a step bound `T` with natural values
that depends on the size alone, and it writes `T(n) = O(n^r)`, for a rational `r = p/q`, as
`T(n)^q ≤ K n^p`.  Here the first bound, rounded up, is shown to be a bound of the second kind
(`bigO_stepBound`), and a program that meets the first is shown to meet the second
(`SolvedInTime.endStatement`).  The program and the slope of the word size stay the same.
-/

public section

namespace ThreeSumApsp.WordRam
open _root_.ThreeSumApsp.WordRam








/-- The rounded bound is `O(n^r)` in the sense of the end statement. -/
theorem bigO_stepBound (C : ℝ) {r : ℚ} (hr0 : 0 ≤ r) : _root_.EndStatement.BigO (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.stepBound C r) r := by
  refine _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.bigO_of_le_rpow (C := 2 * |C| + 1) hr0 fun n hn => ?_
  have hone : (1 : ℝ) ≤ (n : ℝ) ^ (r : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by exact_mod_cast hr0)
  have habs : C * ((n : ℝ) ^ (r : ℝ) + 1) ≤ |C| * ((n : ℝ) ^ (r : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  have hceil : (_root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.stepBound C r n : ℝ) < |C| * ((n : ℝ) ^ (r : ℝ) + 1) + 1 :=
    (Nat.cast_le.2 (Nat.ceil_le_ceil habs)).trans_lt (Nat.ceil_lt_add_one (by positivity))
  -- `|C| (X + 1) + 1 ≤ (2 |C| + 1) X` for `X ≥ 1`
  nlinarith [mul_nonneg (abs_nonneg C) (sub_nonneg.2 hone)]

/-- **A bound `O(n^a)` of an item statement, with `a` the rational `r`, is the bound `O(n^r)` of the
end statement**, with the same program and the same slope. -/
theorem SolvedInTime.endStatement {Q : _root_.EndStatement.Problem} {a : ℝ} (h : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.SolvedInTime Q a 0)
    {r : ℚ} (hr : (r : ℝ) = a) (hr0 : 0 ≤ r) : Q.SolvedInTime r := by
  subst hr
  intro κ
  obtain ⟨P, b, C, hsolves⟩ := h κ
  refine ⟨P, b, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.stepBound C r, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.bigO_stepBound C hr0, fun n x hx W hW => ?_⟩
  obtain ⟨t, ht, verdict, c, hrun, hanswer⟩ := hsolves n x hx W hW
  have ht' : t ≤ _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.stepBound C r n := by
    simp only [pow_zero, mul_one] at ht
    exact_mod_cast ht.trans (Nat.le_ceil _)
  exact ⟨verdict, c, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.exec_mono (c := ⟨0, _⟩) hrun ht', hanswer⟩

end ThreeSumApsp.WordRam

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Arbitrary-length interface for the verified multiplication routine

These exact inequalities convert a requested positive coefficient length
to its power-of-two capacity. Polynomial padding preserves the represented
product. The fifth-power bounds include any fixed linear preparation and
folding overhead, so no real-exponent oracle is needed for the time bound.
-/

namespace ThreeSum.KaratsubaInterface
open _root_.ThreeSum.KaratsubaInterface


open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba
open _root_.ThreeSum.LightKaratsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
open _root_.Polynomial



theorem le_capacity (p : ℕ) : p ≤ _root_.ThreeSum.KaratsubaInterface.capacity p := Nat.le_pow_clog (by decide) p

























end ThreeSum.KaratsubaInterface

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Complete occurrence-by-output local key array

The loop reads the two stored coefficient rows for each schedule occurrence,
constructs every signed local output key, and copies that row into the final
contiguous array. It reuses the row scratch and preserves earlier rows.
-/

namespace ThreeSum.LightLocalKeys
open _root_.ThreeSum.LightLocalKeys


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 2500000
set_option maxRecDepth 10000










variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem time_bound (L n rows : ℕ) : _root_.ThreeSum.LightLocalKeys.time L n rows ≤ 1200*(L+1)*(n+1)*(rows+1) := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalKeyRow.time_bound L n
  have hper : _root_.ThreeSum.LightLocalKeyRow.time L n+_root_.Light.copyTime n+130 ≤ 1100*(L+1)*(n+1) := by
    unfold _root_.Light.copyTime
    nlinarith
  have hm := Nat.mul_le_mul_left rows hper
  have he : 1200*(L+1)*(n+1)*(rows+1) = rows*(1100*(L+1)*(n+1))+20+
      (100*rows*(L+1)*(n+1)+1200*L*n+1200*L+1200*n+1180) := by ring
  unfold _root_.ThreeSum.LightLocalKeys.time
  rw [he]
  omega

end ThreeSum.LightLocalKeys

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



























theorem muZero_square_log_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => (_root_.ThreeSum.Scales.muZero n : ℝ) ^ 2 / Real.log n) atTop (𝓝 0) := by
  have h := (_root_.ThreeSum.Scales.microSize_square_ratio_tendsto_zero.comp _root_.ThreeSum.Scales.inputBits_tendsto_atTop).mul
    _root_.ThreeSum.Scales.inputBits_log_ratio_tendsto
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [_root_.ThreeSum.Scales.inputBits_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (_root_.ThreeSum.Scales.inputBits n : ℝ) ≠ 0 := by exact_mod_cast (by omega : inputBits n ≠ 0)
  simp only [Function.comp_def, _root_.ThreeSum.Scales.muZero]
  field_simp







theorem localSearch_log_ratio_tendsto_zero (C : ℕ) :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum.Scales.localSearch C n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.muZero_square_log_ratio_tendsto_zero.const_mul ((C : ℝ) * Real.log 2)
  simpa [_root_.ThreeSum.Scales.localSearch, Nat.cast_pow, Nat.cast_mul, Real.log_pow, mul_div_assoc,
    mul_comm, mul_left_comm, mul_assoc] using h



/-- Converts a proved logarithmic rate into a power bound; the concrete
table and construction functions are instantiated immediately below. -/
theorem eventually_le_rpow_of_log_ratio {f : ℕ → ℕ} {a d : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a))
    (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (n : ℝ) ^ (a + d) := by
  have hs := hf.eventually (gt_mem_nhds (by linarith : a < a + d))
  filter_upwards [hs, eventually_ge_atTop (2 : ℕ)] with n hn hge
  have hnp : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlog : 0 < Real.log n := Real.log_pos hnp
  exact Real.le_rpow_of_log_le (by linarith) ((div_lt_iff₀ hlog).mp hn).le

theorem localSearch_subpolynomial (C : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (_root_.ThreeSum.Scales.localSearch C n : ℝ) ≤ (n : ℝ) ^ d := by
  simpa using _root_.ThreeSum1960614.Machine.ThreeSum.Scales.eventually_le_rpow_of_log_ratio (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.localSearch_log_ratio_tendsto_zero C) hd









theorem windowExponent_ratio_tendsto_zero :
    Tendsto (fun m : ℕ => (_root_.ThreeSum.Scales.windowExponent m : ℝ) / m) atTop (𝓝 0) := by
  have h := _root_.ThreeSum.Scales.natSqrt_ratio_tendsto_zero.add
    (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  simpa [_root_.ThreeSum.Scales.windowExponent, Nat.cast_add, add_div, one_div] using h





theorem primeWindow_log_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum.Scales.primeWindow n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have h := ((_root_.ThreeSum1960614.Machine.ThreeSum.Scales.windowExponent_ratio_tendsto_zero.comp _root_.ThreeSum.Scales.inputBits_tendsto_atTop).mul
    _root_.ThreeSum.Scales.inputBits_log_ratio_tendsto).const_mul (Real.log 2)
  simp only [zero_mul, mul_zero] at h
  apply h.congr'
  filter_upwards [_root_.ThreeSum.Scales.inputBits_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (_root_.ThreeSum.Scales.inputBits n : ℝ) ≠ 0 := by exact_mod_cast (by omega : inputBits n ≠ 0)
  simp only [Function.comp_def, _root_.ThreeSum.Scales.primeWindow, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  field_simp













theorem muZero_eq_twice_half (n : ℕ) : _root_.ThreeSum.Scales.muZero n = 2 * _root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n) := rfl































































end

end ThreeSum.Scales

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












variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}











theorem time_bound (W n g : ℕ) :
    _root_.ThreeSum.LightColorBands.time W n g ≤ 1200*(W+1)*(n+1)+_root_.ThreeSum.ColorBandBounds.time n g+300 := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.LightColorClasses.time_bound W n
  unfold _root_.ThreeSum.LightColorBands.time
  omega

end ThreeSum.LightColorBands

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# From selected coefficient rows to every original global output key

The fixed program constructs the output-mask layer, all signed local keys,
and the full positional product. Its output is the literal occurrence-aware
`GlobalKeyEnumeration.globalKeys` array. No input key or mask table is assumed.
-/

namespace ThreeSum.LightGlobalKeys
open _root_.ThreeSum.LightGlobalKeys


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress

set_option maxHeartbeats 600000
set_option maxRecDepth 10000


















theorem localCount_pos (h : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount h := by
  apply Nat.mul_pos
  · unfold _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize _root_.ThreeSum.LocalHashMoments.scheduleLength
    positivity
  · exact Nat.choose_pos (by omega)





variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}











theorem time_bound (h J : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.time h J ≤ 2000*(464*h+1)*(_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h+1)*(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h+1)+
      300*(J+1)*(_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount h^J+1)+200 := by
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup.time_bound (464*h) (2*h)
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalKeys.time_bound (464*h) (_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h)
  have hg := _root_.ThreeSum.LightRadixKeys.time_bound (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount h) J (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount_pos h)
  have hc : 800*(464*h+1)*(_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h+1) ≤
      800*(464*h+1)*(_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h+1)*(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  change _root_.ThreeSum.LightSubsetEnumerationSetup.time (464*h) (2*h) ≤
    800*(464*h+1)*(_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h+1) at he
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.time
  nlinarith

end ThreeSum.LightGlobalKeys

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The complete local-cover program fits the uniform local-search budget

Every bound below is for the actual fixed program, including mask and
coefficient construction, counting division, histograms, matrix assembly,
the original greedy loop, and selected-row gathering.
-/

namespace ThreeSum.LightLocalCoverResources
open _root_.ThreeSum.LightLocalCoverResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum.LightLocalCoverMagnitude
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude

set_option maxHeartbeats 1800000



theorem setup_time_polynomial {h B : ℕ} (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude.Bounds h B) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSetup.time h ≤ 11000*B^5 := by
  have hbuild := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCost.build_time_bound H.positive H.width H.vertices H.prime H.candidates H.rounds
  have hp2 : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h ≤ B^2 := by
    have hp := Nat.pow_le_pow_left H.prime 2
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols
    nlinarith
  have hlog := Nat.log_le_self 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h)
  have hB : 1 ≤ B := H.positive
  have hL := H.width
  have hpow15 := Nat.le_self_pow (by decide : 5 ≠ 0) B
  have hpow25 := Nat.pow_le_pow_right hB (by decide : 2 ≤ 5)
  have hB5 : 1 ≤ B^5 := Nat.pow_pos (by omega)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSetup.time _root_.ThreeSum.LightNatPower.time _root_.Light.log2Time
  omega





theorem time_bound (h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSetup.time h ≤ _root_.ThreeSum.LightLocalCoverResources.envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  calc
    _ ≤ 11000*(_root_.ThreeSum.LightLocalCoverMagnitude.magnitude h)^5 := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverResources.setup_time_polynomial (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude.bounds h)
    _ ≤ 2^14*(_root_.ThreeSum.LightLocalCoverMagnitude.magnitude h)^5 := Nat.mul_le_mul_right _ (by decide)
    _ = 2^(14+600000*(h+1)^2*5) := by rw [_root_.ThreeSum.LightLocalCoverMagnitude.magnitude,← pow_mul,← pow_add]
    _ ≤ _root_.ThreeSum.LightLocalCoverResources.envelope h := Nat.pow_le_pow_right (by decide) (by omega)




















end ThreeSum.LightLocalCoverResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual construction of the three lifted original A-key arrays

The middle row is computed by the checked signed remainder routine. Two
affine scans append the minus and plus lifts. Every original position is
retained in each row, and the resulting segment is the exact guarded-key
list whose balancing bound is proved in `RawAKeyLists`.
-/

namespace ThreeSum.LightRawAKeys
open _root_.ThreeSum.LightRawAKeys


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum.RawAKeyLists
open _root_.ThreeSum1960614.Machine.ThreeSum.RawAKeyLists

set_option maxHeartbeats 1000000
set_option maxRecDepth 6000







variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem time_bound (n U : ℕ) : _root_.ThreeSum.LightRawAKeys.time n U ≤ 220*(n+1)*(Nat.log 2 (U+1)+1) := by
  unfold _root_.ThreeSum.LightRawAKeys.time _root_.ThreeSum.LightResidues.residuesTime _root_.ThreeSum.LightResidues.residueBudget _root_.ThreeSum.LightReportingAffine.time
  nlinarith

end ThreeSum.LightRawAKeys

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



















theorem time_bound (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.time n ≤ 1000*(_root_.ThreeSum.Scales.inputBits n+1) := by
  have hu := _root_.ThreeSum1960614.Machine.Light.cbrtLeast_le_self (_root_.ThreeSum.Scales.inputBits n+1)
  have hh := Nat.div_le_self (_root_.Light.cbrtLeast (_root_.ThreeSum.Scales.inputBits n+1)+1) 2
  have hq : 203889696*_root_.ThreeSum.Scales.inputBits n/(20000000000*_root_.ThreeSum.Scales.muZero n) ≤ _root_.ThreeSum.Scales.inputBits n := by
    have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.blockCount_le (_root_.ThreeSum.Scales.inputBits n)
    change 20*(203889696*_root_.ThreeSum.Scales.inputBits n/(20000000000*_root_.ThreeSum.Scales.muZero n)) ≤ 20*_root_.ThreeSum.Scales.inputBits n at hb
    omega
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.time _root_.Light.log2Time _root_.Light.cbrtCeilTime _root_.Light.halfTime _root_.ThreeSum.LightSmallDivide.time
  simp only [_root_.ThreeSum.Scales.inputBits,Nat.log2_eq_log_two] at *
  omega





end ThreeSum.LightScales

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Uniform bounds for repeated modular-counting calls

A caller may reserve resources for the largest modulus it will use. These
lemmas relate that reservation to the exact costed program contract.
-/

namespace ThreeSum.ModuloRuntime
open _root_.ThreeSum.ModuloRuntime


open _root_.ThreeSum.LightModuloCounts
open _root_.ThreeSum1960614.Machine.ThreeSum.LightModuloCounts
open _root_.ThreeSum.KaratsubaInterface
open _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface

theorem capacity_mono {p q : ℕ} (h : p ≤ q) : _root_.ThreeSum.KaratsubaInterface.capacity p ≤ _root_.ThreeSum.KaratsubaInterface.capacity q := by
  exact Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right 2 h)

theorem karatsuba_time_mono : Monotone _root_.ThreeSum.LightKaratsuba.time := by
  apply monotone_nat_of_le_succ
  intro k
  rw [_root_.ThreeSum.LightKaratsuba.time]
  omega

theorem time_mono {p q : ℕ} (h : p ≤ q) (nA nB nC U : ℕ) :
    _root_.ThreeSum.LightModuloCounts.time p nA nB nC U ≤ _root_.ThreeSum.LightModuloCounts.time q nA nB nC U := by
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.ModuloRuntime.capacity_mono h
  have hl := Nat.clog_mono_right 2 h
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.ModuloRuntime.karatsuba_time_mono hl
  unfold _root_.ThreeSum.LightModuloCounts.time _root_.ThreeSum.LightCapacity.time _root_.ThreeSum.LightResidueHistogram.time
    _root_.ThreeSum.LightHistogram.histogramTime _root_.ThreeSum.LightCyclic.combinedTime
  simp only [_root_.Light.fillTime, _root_.ThreeSum.LightArray.linearTime]
  omega









end ThreeSum.ModuloRuntime

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





theorem scheduleCount_log_rate :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n : ℝ) / Real.log n) atTop (𝓝 0) := by
  simpa [_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount] using _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.replicatedHalf_log_rate _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength_log_rate







theorem mu_cast_tendsto_atTop : Tendsto (fun n : ℕ => (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ)) atTop atTop := by
  have hpos : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon / Real.log 2 :=
    div_pos _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon_positive _root_.ThreeSum.Parameters.log_two_pos
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu_log_ratio_tendsto.pos_mul_atTop hpos _root_.ThreeSum.Asymptotics.log_nat_tendsto_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  exact div_mul_cancel₀ _ hlog

theorem mu_tendsto_atTop : Tendsto _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.mu_cast_tendsto_atTop.eventually (eventually_ge_atTop (b : ℝ))] with n hn
  exact_mod_cast hn











end

end ThreeSum.TrimScales

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
# Original input to the retained owner and A-incidence catalog

The selected index coloring, class extraction, normalization, endpoint
construction, three rectangular owner tables, four-cell owner records, and
packed A-incidence rows are all executed by this fixed program. The rows
retain physical owner identities and sorted-array coordinates. Membership
in the original color classes is retained separately by `Represents`.
-/

namespace ThreeSum.LightBandRawAColor
open _root_.ThreeSum.LightBandRawAColor


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists

set_option maxHeartbeats 2400000
set_option maxRecDepth 11000



















variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}











theorem time_bound (W n g : ℕ) :
    _root_.ThreeSum.LightBandRawAColor.time W n g ≤ 1200*(W+1)*(n+1)+_root_.ThreeSum.ColorBandBounds.time n g+_root_.ThreeSum.LightBandRawAColor.catalogTime n g+600 := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.LightColorBands.time_bound W n g
  unfold _root_.ThreeSum.LightBandRawAColor.time
  omega

end ThreeSum.LightBandRawAColor

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Resource bounds for the complete h-and-free local-cover initializer -/

namespace ThreeSum.LightLocalCoverInitResources
open _root_.ThreeSum.LightLocalCoverInitResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout

set_option maxHeartbeats 1500000



theorem parameters_envelope_le (h : ℕ) :
    _root_.ThreeSum.LocalParameterBounds.envelope h ≤ _root_.ThreeSum.LightLocalCoverResources.envelope h := by
  unfold _root_.ThreeSum.LocalParameterBounds.envelope _root_.ThreeSum.LightLocalCoverResources.envelope
  apply Nat.pow_le_pow_right (by decide)
  nlinarith only [Nat.zero_le (h*h)]

theorem constant_le (h : ℕ) : 600 ≤ _root_.ThreeSum.LightLocalCoverResources.envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  exact (by decide : 600 ≤ 2^10).trans
    (Nat.pow_le_pow_right (by decide) (by omega))

theorem four_envelope_le (h : ℕ) :
    4*_root_.ThreeSum.LightLocalCoverResources.envelope h ≤ _root_.ThreeSum.LightLocalCoverInitResources.envelope h := by
  have hs : 1 ≤ (h+1)^2 := Nat.pow_pos (by omega)
  calc
    _ = 2^2*2^(4000000*(h+1)^2) := rfl
    _ = 2^(2+4000000*(h+1)^2) := (pow_add _ _ _).symm
    _ ≤ _root_.ThreeSum.LightLocalCoverInitResources.envelope h := Nat.pow_le_pow_right (by decide) (by omega)

theorem metadata_time_le (h : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSetup.time h+500 := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSetup.time
  omega

theorem time_bound (h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.time h ≤ _root_.ThreeSum.LightLocalCoverInitResources.envelope h := by
  have hp := (_root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.time_bound h).trans (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInitResources.parameters_envelope_le h)
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverResources.time_bound h
  have hm := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInitResources.metadata_time_le h
  have hk := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInitResources.constant_le h
  apply (show _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.time h ≤ 4*_root_.ThreeSum.LightLocalCoverResources.envelope h from ?_).trans
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInitResources.four_envelope_le h)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.time
  omega







theorem envelope_le_search {n : ℕ} (hh : 1 ≤ _root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) :
    _root_.ThreeSum.LightLocalCoverInitResources.envelope (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) ≤ _root_.ThreeSum.Scales.localSearch 5000000 n := by
  unfold _root_.ThreeSum.LightLocalCoverInitResources.envelope _root_.ThreeSum.Scales.localSearch
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.muZero_eq_twice_half]
  apply Nat.pow_le_pow_right (by decide)
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  omega














end ThreeSum.LightLocalCoverInitResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Finite arithmetic-operation bounds for the complete counting backend

The only input-size dependence outside the Karatsuba term is the number of
original elements times their remainder bit budget. Histogram initialization,
capacity computation and folding are included in the displayed constant.
-/

namespace ThreeSum.ModuloCosts
open _root_.ThreeSum.ModuloCosts


open _root_.ThreeSum.KaratsubaInterface
open _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface



theorem capacity_le_roundedPower (p : ℕ) : _root_.ThreeSum.KaratsubaInterface.capacity p ≤ _root_.ThreeSum.ModuloCosts.roundedPower p :=
  Nat.pow_le_pow_left (by decide) _

theorem log_le_roundedPower (p : ℕ) : Nat.clog 2 p ≤ _root_.ThreeSum.ModuloCosts.roundedPower p :=
  (Nat.lt_pow_self (by decide : 1 < 2)).le.trans (_root_.ThreeSum1960614.Machine.ThreeSum.ModuloCosts.capacity_le_roundedPower p)







end ThreeSum.ModuloCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Executing global powers and rounded band sizes

This routine consumes the already computed local output count, local prime,
block count, and total inner size. All global powers, the square-root
rounding, and the final ceiling division are actual Light computations.
The square-root loop and quotient loop are included in the stated time.
-/

namespace ThreeSum.LightGlobalSizes
open _root_.ThreeSum.LightGlobalSizes


set_option maxHeartbeats 1000000

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

















variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}










theorem time_bound (C J mu : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.time C J mu ≤ 1000*(J+mu+_root_.ThreeSum.LightGlobalSizes.root C J+_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.divisor mu+1) := by
  have he : _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.exponent mu ≤ mu := by
    have h := Nat.div_mul_le_self (62656016*mu) 1000000000
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.exponent
    omega
  have hb := Nat.div_le_self (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.numerator C J mu) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.divisor mu)
  have hn : _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.numerator C J mu ≤ _root_.ThreeSum.LightGlobalSizes.root C J+_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.divisor mu := Nat.sub_le _ _
  have hs : Nat.sqrt (C^J-1) ≤ _root_.ThreeSum.LightGlobalSizes.root C J := by unfold _root_.ThreeSum.LightGlobalSizes.root _root_.ThreeSum.LocalCoverBounds.rootCeiling; omega
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.time _root_.ThreeSum.LightNatPower.time _root_.ThreeSum.LightSmallDivide.time _root_.Light.sqrtTime
  omega





theorem localCount_pow (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.localCount n ^ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) = _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n := by
  have hwidth : 232*_root_.ThreeSum.Scales.muZero n = 464*_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n) := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.muZero_eq_twice_half]
    ring
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs
  rw [hwidth,_root_.ThreeSum1960614.Machine.ThreeSum.Scales.muZero_eq_twice_half]
  rfl



end ThreeSum.LightGlobalSizes

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The executable integer quartic switch

The implementation scans integers `q ≤ r/2` and tests a cleared integer
inequality.  No real-number comparison, logarithm oracle, or unbounded
noncomputable search occurs in the definition.  For admissible depths the
candidate set is nonempty.  Minimality gives the exact `9/r` rounding error
needed by the certified box and entropy bounds.
-/

namespace ThreeSum.Switch
open _root_.ThreeSum.Switch


open _root_.Set
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales

set_option maxHeartbeats 0

























noncomputable section



























theorem actual_totalSize (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n = _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) * _root_.ThreeSum.Scales.muZero n := rfl



theorem actual_depth_condition {n j : ℕ} (hj : j ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) :
    20 * j ≤ 13 * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) := by
  have hm := Nat.div_mul_le_self (13 * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) 20
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth at hj
  omega









end
end ThreeSum.Switch

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
# Finite sums and asymptotic bounds for the actual hierarchy

The finite box and query counts are summed over the executable depth range.
The only envelopes introduced here are explicit elementary functions of the
already constructed integer `mu`; all growth rates are proved from Scales.
-/

namespace ThreeSum.HierarchyScales
open _root_.ThreeSum.HierarchyScales


open _root_.Filter
open _root_.Set
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Switch
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open scoped _root_.Topology
open scoped _root_.BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000













theorem terminalDepth_le_mu {n : ℕ} (hmu : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) : _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
  have hprod := hmu
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_totalSize] at hprod
  have hm := Nat.pos_of_mul_pos_left hprod
  have hc := Nat.mul_le_mul_left (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (show 1 ≤ _root_.ThreeSum.Scales.muZero n by omega)
  have hd := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_depth_condition (n := n) (j := _root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n) le_rfl
  rw [Nat.mul_one, ← _root_.ThreeSum1960614.Machine.ThreeSum.Switch.actual_totalSize] at hc
  omega

noncomputable section



theorem allPrefixBoxes_envelope {n : ℕ} (hmu : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allPrefixBoxes n : ℝ) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.hierarchyEnvelope (2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving) 0 n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allPrefixBoxes
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n + 1),
        Real.exp ((_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ) * Real.log 2 * (2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact Real.le_exp_of_log_le (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixBoxes_log_bound hmu (by simpa using hj))
    _ = (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.terminalDepth n + 1 : ℝ) *
        Real.exp ((_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ) * Real.log 2 * (2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving)) := by simp
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.hierarchyEnvelope (2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving) 0 n := by
      simp only [_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.hierarchyEnvelope, add_zero]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact_mod_cast Nat.add_le_add_right (_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.terminalDepth_le_mu hmu) 1







theorem eventually_real_le_rpow_of_log_rate {f : ℕ → ℝ} {a d : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n) / Real.log n) atTop (𝓝 a)) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, f n ≤ (n : ℝ) ^ (a + d) := by
  have hs := hf.eventually (gt_mem_nhds (by linarith : a < a + d))
  filter_upwards [hs, eventually_ge_atTop (2 : ℕ)] with n hn hge
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  exact Real.le_rpow_of_log_le (by exact_mod_cast (by omega : 0 < n))
    ((div_lt_iff₀ hlog).mp hn).le

theorem allPrefixBoxes_eventually_le {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allPrefixBoxes n : ℝ) ≤
      (n : ℝ) ^ (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving) + d) := by
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.eventually_real_le_rpow_of_log_rate
    (_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.hierarchyEnvelope_log_rate (2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving) 0) hd
  filter_upwards [he, _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.mu_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn hmu
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.allPrefixBoxes_envelope (by omega : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)).trans hn

































end
end ThreeSum.HierarchyScales

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







theorem scheduleCount_pos (n : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n :=
  Nat.pow_pos (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength_pos _)

theorem bandCount_pos {n : ℕ} (hn : 0 < n) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n :=
  Nat.pos_of_mul_pos_left (hn.trans_le (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount_mul_bounds n).1)

theorem rawTripleBound_pos {n : ℕ} (hn : 0 < n) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.rawTripleBound n := by
  have hB := _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.bandCount_pos hn
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.rawTripleBound
  positivity

theorem wantedNumerator_pos {n : ℕ} (hn : 0 < n) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.wantedNumerator n := by
  have hS := _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.scheduleCount_pos n
  have hM := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.typedOutputs_pos n
  have hB := _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.bandCount_pos hn
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hS) hM)
    (Nat.pow_pos hB)) hb

theorem scoreLoss_pos (k n : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.scoreLoss k n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.scoreLoss
  positivity

theorem primeLoss_pos (n : ℕ) : 0 < _root_.ThreeSum.Scales.primeLoss _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n := by
  have hy := _root_.ThreeSum.Scales.primeWindow_ge_two n
  unfold _root_.ThreeSum.Scales.primeLoss
  positivity

theorem candidateCount_eventually_pos : ∀ᶠ n : ℕ in atTop, 0 < _root_.ThreeSum.Scales.candidateCount n := by
  filter_upwards [_root_.ThreeSum.Scales.actual_candidates_nonempty] with n hn
  exact Finset.card_pos.mpr hn

theorem falseNumerator_eventually_pos (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, 0 < _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseNumerator k n := by
  filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.candidateCount_eventually_pos, eventually_ge_atTop (1 : ℕ)] with n hC hn
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.rawTripleBound_pos (by omega : 0 < n)
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.scoreLoss_pos k n
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.primeLoss_pos n
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseNumerator
  positivity

noncomputable section





theorem nat_log_rate_const (c : ℕ) :
    Tendsto (fun n : ℕ => Real.log (c : ℝ) / Real.log n) atTop (𝓝 0) := by
  simpa only [mul_zero, Pi.inv_apply, div_eq_mul_inv] using
    _root_.ThreeSum.Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log (c : ℝ))

theorem nat_log_rate_mul {f g : ℕ → ℕ} {a b : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a))
    (hg : Tendsto (fun n : ℕ => Real.log (g n : ℝ) / Real.log n) atTop (𝓝 b))
    (hp : ∀ᶠ n : ℕ in atTop, 0 < f n ∧ 0 < g n) :
    Tendsto (fun n : ℕ => Real.log ((f n * g n : ℕ) : ℝ) / Real.log n) atTop (𝓝 (a + b)) := by
  apply (hf.add hg).congr'
  filter_upwards [hp] with n hn
  have hfR : (f n : ℝ) ≠ 0 := by exact_mod_cast hn.1.ne'
  have hgR : (g n : ℝ) ≠ 0 := by exact_mod_cast hn.2.ne'
  simp only [Nat.cast_mul, Real.log_mul hfR hgR, add_div]

theorem nat_log_rate_pow {f : ℕ → ℕ} {a : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a)) (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log ((f n ^ k : ℕ) : ℝ) / Real.log n) atTop (𝓝 ((k : ℝ) * a)) := by
  simpa only [Nat.cast_pow, Real.log_pow, mul_div_assoc] using hf.const_mul (k : ℝ)





theorem bandSize_log_rate_shift :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n : ℝ) / Real.log n) atTop
      (𝓝 (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))) := by
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift, sub_eq_add_neg] using _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_log_rate

theorem wantedNumerator_log_rate :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.wantedNumerator n : ℝ) / Real.log n) atTop
      (𝓝 (2 + 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))) := by
  have h1 := _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.nat_log_rate_mul (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.nat_log_rate_const 9) _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount_log_rate (by
    filter_upwards [] with n
    exact ⟨by norm_num, _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.scheduleCount_pos n⟩)
  have h2 := _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.nat_log_rate_mul h1 _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs_log_ratio_tendsto (by
    filter_upwards [] with n
    exact ⟨Nat.mul_pos (by norm_num) (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.scheduleCount_pos n), _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.typedOutputs_pos n⟩)
  have h3 := _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.nat_log_rate_mul h2 (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.nat_log_rate_pow _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.bandCount_log_rate 2) (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact ⟨Nat.mul_pos (Nat.mul_pos (by norm_num) (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.scheduleCount_pos n)) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.typedOutputs_pos n),
      Nat.pow_pos (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.bandCount_pos (by omega))⟩)
  have h4 := _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.nat_log_rate_mul h3 _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.bandSize_log_rate_shift (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    refine ⟨?_, _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_pos n⟩
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.scheduleCount_pos n))
      (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.typedOutputs_pos n)) (Nat.pow_pos (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.bandCount_pos (by omega))))
  convert h4 using 1 <;> simp only [_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.wantedNumerator, Nat.cast_ofNat] <;> ring





theorem wantedMajorant_log_rate :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.wantedMajorant n) / Real.log n) atTop
      (𝓝 (2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))) := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.wantedNumerator_log_rate.sub _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_log_ratio_tendsto
  have hid : (2 + 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 1 / 2) =
      2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift) := by ring
  rw [hid] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hN : (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.wantedNumerator n : ℝ) ≠ 0 := by exact_mod_cast (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.wantedNumerator_pos (by omega : 0 < n)).ne'
  have hR : (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n : ℝ) ≠ 0 := by exact_mod_cast (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n).ne'
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.wantedMajorant, Real.log_div hN hR, sub_div]

theorem falseMajorant_log_rate (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseMajorant k n) / Real.log n) atTop
      (𝓝 (2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))) := by
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseNumerator_log_rate k).sub _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_log_ratio_tendsto
  have hid : (2 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 1 / 2) =
      2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift) := by ring
  rw [hid] at hh
  apply hh.congr'
  filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseNumerator_eventually_pos k] with n hn
  have hN : (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseNumerator k n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hR : (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n : ℝ) ≠ 0 := by exact_mod_cast (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n).ne'
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseMajorant, Real.log_div hN hR, sub_div]

theorem wantedMajorant_eventually_le {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.wantedMajorant n ≤ (n : ℝ) ^ (2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift) + d) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.eventually_real_le_rpow_of_log_rate _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.wantedMajorant_log_rate hd

theorem falseMajorant_eventually_le (k : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseMajorant k n ≤ (n : ℝ) ^ (2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift) + d) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.eventually_real_le_rpow_of_log_rate (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseMajorant_log_rate k) hd

theorem wanted_mass_le {n W : ℕ} (hW : W * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.wantedNumerator n) :
    (W : ℝ) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.wantedMajorant n := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.wantedMajorant, le_div_iff₀ (show (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n by exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)]
  exact_mod_cast hW



end
end ThreeSum.MassScales

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The six principal finite stage counts

This module assembles actual natural-number work quantities.  Its final
theorem is a runtime-ledger target, not a 3SUM correctness or machine-time
theorem.  The only input-dependent assumptions are four explicit finite
counting inequalities for the wanted mass and the prime-chain score.
An implementation must still connect its operation counter to these counts.
-/

namespace ThreeSum.StageBounds
open _root_.ThreeSum.StageBounds


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
open scoped _root_.Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000





















noncomputable section



namespace PowerBound
open _root_.ThreeSum.StageBounds.PowerBound


theorem of_rate {f : ℕ → ℕ} {a : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a)) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a :=
  fun _ hd => _root_.ThreeSum1960614.Machine.ThreeSum.Scales.eventually_le_rpow_of_log_ratio hf hd

theorem const (c : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun _ => c) 0 := _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.nat_log_rate_const c)

theorem mul {f g : ℕ → ℕ} {a b : ℝ} (hf : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a) (hg : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound g b) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => f n * g n) (a + b) := by
  intro d hd
  filter_upwards [hf (d / 2) (by linarith), hg (d / 2) (by linarith),
    eventually_ge_atTop (1 : ℕ)] with n hfn hgn hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [Nat.cast_mul]
  calc
    _ ≤ (n : ℝ) ^ (a + d / 2) * (n : ℝ) ^ (b + d / 2) :=
      mul_le_mul hfn hgn (Nat.cast_nonneg _) (Real.rpow_nonneg hnR.le _)
    _ = (n : ℝ) ^ ((a + b) + d) := by rw [← Real.rpow_add hnR]; congr 1; ring

theorem mono_exponent {f : ℕ → ℕ} {a b : ℝ} (hf : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a) (hab : a ≤ b) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f b := by
  intro d hd
  filter_upwards [hf d hd, eventually_ge_atTop (1 : ℕ)] with n hn hge
  exact hn.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hge) (by linarith))



theorem pow {f : ℕ → ℕ} {a : ℝ} (hf : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a) (k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => f n ^ k) ((k : ℝ) * a) := by
  induction k with
  | zero => simpa only [Nat.cast_zero, zero_mul, pow_zero] using _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1
  | succ k ih =>
      simpa only [Nat.pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul hf

end PowerBound

theorem wanted_powerBound {W : ℕ → ℕ}
    (hW : ∀ᶠ n : ℕ in atTop, W n * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.wantedNumerator n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound W (2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) := by
  intro d hd
  filter_upwards [hW, _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.wantedMajorant_eventually_le hd] with n hn he
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.wanted_mass_le hn).trans he





theorem encoder_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoderCount (1 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) := by
  have hh := (((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 2).mul (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.bandCount_log_rate)).mul
    (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount_log_rate)).mul (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.fullOutputs_log_rate)
  have heq : ((0 : ℝ) + (1 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) + 0) + 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E =
      1 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift) := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon; ring
  rw [heq] at hh
  exact hh

theorem boxes_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.boxCount (2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving) := by
  have hB := _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.nat_log_rate_pow _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.bandCount_log_rate 2)
  have hQ : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.allPrefixBoxes (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving)) :=
    fun _ hd => _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.allPrefixBoxes_eventually_le hd
  have hh := (((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 3).mul hB).mul (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount_log_rate)).mul hQ
  have heq : ((0 : ℝ) + 2 * (1 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) + 0) +
      _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving) = 2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon; ring
  norm_num only [Nat.cast_ofNat] at hh
  rw [heq] at hh
  exact hh

theorem initial_powerBound {W : ℕ → ℕ}
    (hW : ∀ᶠ n : ℕ in atTop, W n * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.wantedNumerator n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.initialCount W) (2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift - _root_.ThreeSum.Parameters.entropy _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta)) := by
  have hQ : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.queryTerms n 0) (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * _root_.ThreeSum.Parameters.entropy _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta) :=
    fun _ hd => _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.initial_query_eventually_le hd
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.wanted_powerBound hW).mul hQ
  have heq : (2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * _root_.ThreeSum.Parameters.entropy _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta =
      2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift - _root_.ThreeSum.Parameters.entropy _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta) := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon; ring
  rw [heq] at hh
  exact hh





















end
end ThreeSum.StageBounds

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















theorem cutoff_eq (n : ℕ) :
    2*_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) = _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize _root_.ThreeSum.Scales.microSize _root_.ThreeSum.Scales.microHalf
  ring

















end ThreeSum.BlockSourceSharing

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









theorem wantedBudget_mul_le (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.wantedBudget n * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.wantedNumerator n :=
  Nat.div_mul_le_self _ _

noncomputable section



theorem wantedBudget_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.wantedBudget (2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.wanted_powerBound (Filter.Eventually.of_forall _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.wantedBudget_mul_le)

theorem falseBudget_powerBound (k : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (_root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.falseBudget k) (2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) := by
  intro d hd
  filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseMajorant_eventually_le k hd] with n hn
  have hb : (_root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.falseBudget k n : ℝ) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseMajorant k n := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseMajorant, le_div_iff₀ (show (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n by exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)]
    exact_mod_cast Nat.div_mul_le_self (_root_.ThreeSum1960614.Machine.ThreeSum.MassScales.falseNumerator k n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n)
  exact hb.trans hn

theorem budget_initial_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.initialCount _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.wantedBudget)
      (2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift - _root_.ThreeSum.Parameters.entropy _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta)) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.initial_powerBound (Filter.Eventually.of_forall _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.wantedBudget_mul_le)



theorem budget_terminal_powerBound (k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalCount (_root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.falseBudget k))
      (2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction - 1 / 2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa)) := by
  have hh := (((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 2).mul (_root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.falseBudget_powerBound k)).mul
    (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.representationBound_log_rate)).mul (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalChoices_log_rate)
  have heq : ((0 : ℝ) + (2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa) +
      _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction) =
      2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction - 1 / 2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa) := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon; ring
  rw [heq] at hh
  exact hh





















end
end ThreeSum.UniformStageBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The arithmetic and balancing work outside the six reporting stages

The finite bounds here include complete modular-counting invocations, their
signed-remainder bit cost, and the actual correlation/minimum routine. They
augment the six-stage reporting budget. The whole solver still has to charge
its actual host operations to this combined budget.
-/

namespace ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.ArithmeticStageBounds


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales
open _root_.ThreeSum.MassScales
open _root_.ThreeSum1960614.Machine.ThreeSum.MassScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds
open _root_.ThreeSum.ModuloCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.ModuloCosts
open scoped _root_.Topology

set_option maxHeartbeats 1000000

















theorem bits_le_window_square (n : ℕ) : _root_.ThreeSum.Scales.inputBits n+1 ≤ _root_.ThreeSum.Scales.primeWindow n^2 := by
  have hroot := Nat.lt_succ_sqrt' (_root_.ThreeSum.Scales.inputBits n)
  have hpow : Nat.sqrt (_root_.ThreeSum.Scales.inputBits n)+1 ≤ 2^(Nat.sqrt (_root_.ThreeSum.Scales.inputBits n)+1) :=
    (Nat.lt_pow_self (by decide : 1 < 2)).le
  have hs := Nat.pow_le_pow_left hpow 2
  unfold _root_.ThreeSum.Scales.primeWindow _root_.ThreeSum.Scales.windowExponent
  simp only [Nat.succ_eq_add_one] at hroot
  omega

theorem remainder_bits_le {n : ℕ} (k : ℕ) (hn : 0 < n) :
    Nat.log 2 (n^k+1)+1 ≤ _root_.ThreeSum.ArithmeticStageBounds.bitBudget k n := by
  have hp : 0 < n^k := Nat.pow_pos hn
  have hm := Nat.log_mono_right (b := 2) (show n^k+1 ≤ 3*n^k by omega)
  have hl := _root_.ThreeSum.Scales.log2_difference_bound k hn
  rw [Nat.log2_eq_log_two] at hl
  have hw := Nat.mul_le_mul_left (2*(k+2)) (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.bits_le_window_square n)
  unfold _root_.ThreeSum.ArithmeticStageBounds.bitBudget
  omega

theorem invocation_le_budget {n p nA nB nC : ℕ} (k : ℕ)
    (hn : 0 < n) (hp : p ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n)
    (ha : nA ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (hb : nB ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (hc : nC ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) :
    _root_.ThreeSum.LightModuloCounts.time p nA nB nC (n^k) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTripleBudget k n := by
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.ModuloRuntime.time_mono hp nA nB nC (n^k)
  have hbnd := _root_.ThreeSum.ModuloCosts.time_bound (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) nA nB nC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (n^k) ha hb hc
  have hm := Nat.mul_le_mul_left (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.remainder_bits_le k hn)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTripleBudget
  omega

noncomputable section

theorem powerBound_mono {f g : ℕ → ℕ} {a : ℝ} (hg : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound g a)
    (hfg : ∀ᶠ n : ℕ in atTop, f n ≤ g n) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a := by
  intro d hd
  filter_upwards [hg d hd, hfg] with n hn hm
  exact (show (f n : ℝ) ≤ (g n : ℝ) by exact_mod_cast hm).trans hn



theorem window_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum.Scales.primeWindow 0 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate _root_.ThreeSum1960614.Machine.ThreeSum.Scales.primeWindow_log_ratio_tendsto_zero

theorem maxMod_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+1/2)) := by
  change _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n*(4*_root_.ThreeSum.Scales.primeWindow n)^2) (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+1/2))
  have hwindow := ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 4).mul _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.window_powerBound).pow 2
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_log_ratio_tendsto).mul hwindow
  simpa only [zero_add, mul_zero, add_zero] using hh



theorem bitBudget_powerBound (k : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (_root_.ThreeSum.ArithmeticStageBounds.bitBudget k) 0 := by
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const (2*(k+2))).mul (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.window_powerBound.pow 2)
  have hh' : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 2*(k+2)*_root_.ThreeSum.Scales.primeWindow n^2) 0 := by
    simpa only [Nat.cast_ofNat, mul_zero, add_zero] using hh
  exact hh'.add_same (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)







theorem identity_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n : ℕ => n) 1 := by
  intro d hd
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simpa only [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_le hnR (show (1 : ℝ) ≤ 1+d by linarith))















end
end ThreeSum.ArithmeticStageBounds

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
# Charge the executed common-prime setup

The bound includes the generated pool, every aggregate candidate minimum,
all original band-score calls, and the computed chain depth. The size-only
budget uses the same quadratic owner bound as the physical mass theorem.
-/

namespace ThreeSum.BandPrimeCosts
open _root_.ThreeSum.BandPrimeCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000





















theorem unit_le_budget {n : ℕ} (k : ℕ) (hn : 0 < n) :
    _root_.ThreeSum.BandPrimeCosts.unit (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (n^k) ≤ 3*_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTripleBudget k n := by
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.invocation_le_budget (p := _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) k hn le_rfl le_rfl le_rfl le_rfl
  have hp := (_root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface.le_capacity (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n)).trans (_root_.ThreeSum1960614.Machine.ThreeSum.ModuloCosts.capacity_le_roundedPower (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n))
  have hl : Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n+1) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n+1 := Nat.log_le_self _ _
  have hj : _root_.ThreeSum.LightWeightedScore.jointTime (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTripleBudget k n := by
    unfold _root_.ThreeSum.LightWeightedScore.jointTime _root_.ThreeSum.LightResidues.residueBudget _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTripleBudget
    omega
  have hlarge : 1000 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTripleBudget k n := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTripleBudget; omega
  unfold _root_.ThreeSum.BandPrimeCosts.unit
  omega





end ThreeSum.BandPrimeCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Original-size resource envelope for the actual source-header adapter -/

namespace ThreeSum.EncodedColorSourcesCosts
open _root_.ThreeSum.EncodedColorSourcesCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales





theorem time_eq (n p U M : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorSourcesCosts.time n p U M=_root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.time n p U M+20*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)+1020 := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorSourcesCosts.time _root_.ThreeSum.LightNatPower.time
  omega

end ThreeSum.EncodedColorSourcesCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exponent of the complete shared-catalog invocation budget

The local balanced-pair enumeration and all polynomial factors in the
concrete52-procedure constructor have exponent zero. Multiplying the
existing box ledger by this overhead therefore preserves its exponent.
This charges catalog invocations; the surrounding bank iterator is separate.
-/

namespace ThreeSum.SharedReportingCosts
open _root_.ThreeSum.SharedReportingCosts


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open scoped _root_.Topology

set_option maxHeartbeats 1500000

noncomputable section

theorem bits_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum.Scales.inputBits 0 := by
  have hh : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum.Scales.primeWindow n^2) 0 := by
    simpa only [mul_zero] using _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.window_powerBound.pow 2
  exact _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono hh (Eventually.of_forall fun n => by
    have h := _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.bits_le_window_square n
    omega)

theorem half_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum.SharedReportingCosts.half 0 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.bits_powerBound (Eventually.of_forall fun n =>
    _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.microHalf_le_self (_root_.ThreeSum.Scales.inputBits n))

theorem blocks_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks 0 := by
  have hh : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 20*_root_.ThreeSum.Scales.inputBits n) 0 := by
    simpa only [zero_add] using (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 20).mul _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.bits_powerBound
  exact _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono hh (Eventually.of_forall fun n =>
    _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.blockCount_le (_root_.ThreeSum.Scales.inputBits n))

theorem local_width_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.localWidth 0 := by
  change _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 464*_root_.ThreeSum.SharedReportingCosts.half n) 0
  simpa only [zero_add] using (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 464).mul _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.half_powerBound

theorem width_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.width 0 := by
  change _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.localWidth n) 0
  simpa only [zero_add] using _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks_powerBound.mul _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.local_width_powerBound













end
end ThreeSum.SharedReportingCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exponent bound for the actual common-prime setup budget

The candidate pool and number of minimum rounds contribute only a
subpolynomial factor. This proves the arithmetic term for the executed
aggregate program; it does not assert completion of the whole solver.
-/

namespace ThreeSum.BandPrimeCosts
open _root_.ThreeSum.BandPrimeCosts


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open scoped _root_.Topology

set_option maxHeartbeats 1400000

noncomputable section







theorem owner_count_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 3*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2+1) (2*(1-_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))) := by
  have hc := (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 3).mul ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales.bandCount_log_rate).pow 2)
  have hc' : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 3*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2) (2*(1-_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))) := by
    simpa only [Nat.cast_ofNat,zero_add] using hc
  have he : (0 : ℝ) ≤ 2*(1-_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) := by
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E_bounds.2
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon
    linarith
  exact hc'.add_same ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1).mono_exponent he)



theorem timeBudget_certificate (k : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.timeBudget k) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.timeBudget_powerBound k).mono_exponent (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.all_costs_le_raw_exponent _ (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.costLedger]))





end
end ThreeSum.BandPrimeCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Finite and asymptotic cost of executing the small coloring family -/

namespace ThreeSum.LightColorParametersCosts
open _root_.ThreeSum.LightColorParametersCosts


open _root_.ThreeSum.ColorParameters
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorParameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds













open _root_.Filter
open _root_.Real
open scoped _root_.Topology

noncomputable section

theorem width_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum.LightColorParametersCosts.width 0 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.bits_powerBound.add_same (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)

theorem count_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum.ColorParameters.count (_root_.ThreeSum.LightColorParametersCosts.width n)) 0 := by
  simpa only [_root_.ThreeSum.ColorParameters.count,mul_zero,zero_add] using (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 81).mul (_root_.ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts.width_powerBound.pow 2)





end
end ThreeSum.LightColorParametersCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Uniform finite and exponent bounds for the actual switch controls -/

namespace ThreeSum.LightSwitchCosts
open _root_.ThreeSum.LightSwitchCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.Filter
open scoped _root_.Topology


















noncomputable section

theorem time_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchCosts.timeBudget 0 := by
  have hh := ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 200).mul
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.bits_powerBound.add_same (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)))
  have hh' : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 200*(_root_.ThreeSum.Scales.inputBits n+1)) 0 := by
    simpa only [zero_add] using hh
  exact hh'.add_same (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 100)

theorem depth_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum.LightSwitchCosts.depthBudget 0 := by
  have hh : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 5200*_root_.ThreeSum.Scales.inputBits n) 0 := by
    simpa only [zero_add] using (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 5200).mul _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.bits_powerBound
  exact hh.add_same (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 90)





end
end ThreeSum.LightSwitchCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The physical reporting catalogs use the certified traversal ledger

The switch in every retained catalog is the literal switch used by the
original finite ledger. This module connects the executed level and terminal
costs to those exact binomial terms, preserving the sum over levels.
-/

namespace ThreeSum.SharedTraversalCosts
open _root_.ThreeSum.SharedTraversalCosts


open _root_.Finset
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open scoped _root_.BigOperators

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000

































open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open scoped _root_.Topology

noncomputable section

theorem size_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum.SharedTraversalCosts.size (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n)) 0 := by
  have hh : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum.SharedTraversalCosts.half 0 := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.half_powerBound
  have hj : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks 0 := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks_powerBound
  have hl : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 2048*_root_.ThreeSum.SharedTraversalCosts.half n+20) 0 := by
    have hm : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 2048*_root_.ThreeSum.SharedTraversalCosts.half n) 0 := by
      simpa only [zero_add] using (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 2048).mul hh
    exact hm.add_same (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 20)
  change _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n+1)*(2048*_root_.ThreeSum.SharedTraversalCosts.half n+20)) 0
  simpa only [zero_add] using (hj.add_same (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)).mul hl

theorem overhead_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scaledOverhead 0 := by
  change _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 200000*(_root_.ThreeSum.SharedTraversalCosts.size (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n))^4) 0
  simpa only [zero_add,mul_zero] using (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 200000).mul (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.size_powerBound.pow 4)

theorem traversal_counts_powerBound (k : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound
    (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.initialCount _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.wantedBudget n+
      _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.activeCount (_root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.falseBudget k) n+
      _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalCount (_root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.falseBudget k) n) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent := by
  have hi := _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.budget_initial_powerBound.mono_exponent
    (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.all_costs_le_raw_exponent _ (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.costLedger]))
  have ha := (_root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.budget_active_powerBound k).mono_exponent
    (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.all_costs_le_raw_exponent _ (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.costLedger]))
  have ht := (_root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.budget_terminal_powerBound k).mono_exponent
    (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.all_costs_le_raw_exponent _ (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.costLedger]))
  exact (hi.add_same ha).add_same ht





end
end ThreeSum.SharedTraversalCosts

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

theorem core_time_eq (maxMod g R M y U : ℕ) :
    _root_.ThreeSum.LightEncodedColorPrimeCore.time maxMod g R M y U=
      _root_.ThreeSum.LightBandPrimeSetup.time maxMod g R M y U+760 := by
  unfold _root_.ThreeSum.LightEncodedColorPrimeCore.time _root_.ThreeSum.LightBandPrimeSetup.time _root_.ThreeSum.LightBandPrimeConstruction.time
  omega

theorem time_eq (maxMod nA nB nC g M y U : ℕ) :
    _root_.ThreeSum.LightEncodedColorPrime.time maxMod nA nB nC g M y U=
      _root_.ThreeSum.LightBandPrimeSetup.time maxMod g (_root_.ThreeSum.LightEncodedColorPrime.count nA nB nC g) M y U+1160 := by
  rw [_root_.ThreeSum.LightEncodedColorPrime.time,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts.core_time_eq]







theorem count_le {nA nB nC n : ℕ} (ha : nA ≤ n) (hb : nB ≤ n) (hc : nC ≤ n) :
    _root_.ThreeSum.LightEncodedColorPrime.count nA nB nC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) ≤ 3*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2 := by
  have a := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.size_le_bandCount ha
  have b := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.size_le_bandCount hb
  have c := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.size_le_bandCount hc
  have ab := Nat.mul_le_mul a b
  have ac := Nat.mul_le_mul a c
  have bc := Nat.mul_le_mul b c
  unfold _root_.ThreeSum.LightEncodedColorPrime.count
  nlinarith

theorem time_le_budget {nA nB nC n : ℕ} (k : ℕ) (hn : 0 < n)
    (ha : nA ≤ n) (hb : nB ≤ n) (hc : nC ≤ n) :
    _root_.ThreeSum.LightEncodedColorPrime.time (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) nA nB nC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.Scales.primeWindow n) (n^k) ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.timeBudget k n+1160 := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts.time_eq]
  exact Nat.add_le_add_right (_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.setup_time_le_budget k hn (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts.count_le ha hb hc)) 1160









end ThreeSum.EncodedColorPrimeCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # The finite color scan preserves a per-color power bound -/

namespace ThreeSum.LightColorScanCosts
open _root_.ThreeSum.LightColorScanCosts


open _root_.ThreeSum.ColorParameters
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorParameters
open _root_.ThreeSum.LightColorParametersCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds

noncomputable section

theorem time_powerBound {T : ℕ → ℕ} {a : ℝ} (hT : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound T a) (ha : 0 ≤ a) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum.LightColorScanHost.time (T n) n) a := by
  have h100 : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 100*_root_.ThreeSum.ColorParameters.count (_root_.ThreeSum.LightColorParametersCosts.width n)) 0 := by
    simpa only [zero_add] using (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 100).mul _root_.ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts.count_powerBound
  have hround : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 100*_root_.ThreeSum.ColorParameters.count (_root_.ThreeSum.LightColorParametersCosts.width n)+T n+3000) a :=
    ((h100.mono_exponent ha).add_same hT).add_same ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 3000).mono_exponent ha)
  have hmul : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum.ColorParameters.count (_root_.ThreeSum.LightColorParametersCosts.width n)*(100*_root_.ThreeSum.ColorParameters.count (_root_.ThreeSum.LightColorParametersCosts.width n)+T n+3000)) a := by
    simpa only [zero_add] using _root_.ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts.count_powerBound.mul hround
  change _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum.ColorParameters.count (_root_.ThreeSum.LightColorParametersCosts.width n)*(100*_root_.ThreeSum.ColorParameters.count (_root_.ThreeSum.LightColorParametersCosts.width n)+T n+3000)+100+100) a
  exact (hmul.add_same ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 100).mono_exponent ha)).add_same
    ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 100).mono_exponent ha)





end
end ThreeSum.LightColorScanCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Charge the actual threshold construction

One final aggregate score is covered by the existing executed arithmetic
budget. Computing the cap and storing its product adds only O(J) work.
This is a cost theorem for this concrete stage, not a full solver claim.
-/

namespace ThreeSum.LightDenseSetupCosts
open _root_.ThreeSum.LightDenseSetupCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters

set_option maxHeartbeats 1400000
set_option maxRecDepth 8000

theorem aggregate_time_le_budget {n R : ℕ} (k : ℕ) (hn : 0 < n)
    (hR : R ≤ 3*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2) :
    _root_.ThreeSum.LightBandWeightedScore.time (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) R
      (_root_.ThreeSum.LightPrimePool.size (_root_.ThreeSum.Scales.primeWindow n)) (n^k) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.timeBudget k n := by
  let s := _root_.ThreeSum.LightPrimePool.size (_root_.ThreeSum.Scales.primeWindow n)
  have hs : s+1 ≤ (s+1)^2 := by nlinarith
  have hd : 6 ≤ 15*(_root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n+1) := by omega
  have ht := _root_.ThreeSum.BandPrimeCosts.aggregate_time_le (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) R s (n^k)
  have hu := _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.unit_le_budget k hn
  calc
    _ ≤ 2*(R+1)*(s+1)*_root_.ThreeSum.BandPrimeCosts.unit (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (n^k) := ht
    _ ≤ 2*(3*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2+1)*(s+1)*(3*_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTripleBudget k n) := by gcongr
    _ = 6*((3*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2+1)*((s+1)*_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTripleBudget k n)) := by ring
    _ ≤ (15*(_root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n+1))*
        ((3*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2+1)*((s+1)^2*_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTripleBudget k n)) :=
      Nat.mul_le_mul hd (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hs))
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.timeBudget k n := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.timeBudget; dsimp [s]; nlinarith



theorem time_le_budget {n R : ℕ} (k : ℕ) (hn : 0 < n)
    (hR : R ≤ 3*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2) :
    _root_.ThreeSum.LightDenseSetup.time (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) R (_root_.ThreeSum.LightPrimePool.size (_root_.ThreeSum.Scales.primeWindow n))
      (n^k) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetupCosts.timeBudget k n := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetupCosts.aggregate_time_le_budget k hn hR
  unfold _root_.ThreeSum.LightDenseSetup.time _root_.ThreeSum.LightDenseCap.time _root_.ThreeSum.LightNatPower.time _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetupCosts.timeBudget
  omega

open _root_.Filter
open _root_.Real
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open scoped _root_.Topology

noncomputable section

theorem scalar_time_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 20*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)+570) 0 := by
  have hj := (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 20).mul _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks_powerBound
  have hj' : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 20*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) 0 := by
    simpa only [zero_add,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks] using hj
  exact hj'.add_same (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 570)

theorem timeBudget_powerBound (k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetupCosts.timeBudget k) (2+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(4/5-(2/5)*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E-2*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) := by
  change _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.timeBudget k n+20*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)+570)
    (2+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(4/5-(2/5)*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E-2*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))
  have he : (0 : ℝ) ≤ 2+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(4/5-(2/5)*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E-2*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift) := by
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E_bounds.2
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift
    linarith
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.timeBudget_powerBound k).add_same (_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetupCosts.scalar_time_powerBound.mono_exponent he)
  simpa only [Nat.add_assoc] using hh

theorem timeBudget_certificate (k : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetupCosts.timeBudget k) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetupCosts.timeBudget_powerBound k).mono_exponent (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.all_costs_le_raw_exponent _ (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.costLedger]))



end
end ThreeSum.LightDenseSetupCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Charge the executed shared catalog bank, including every surrounding loop

The exact sum of level costs is preserved. Actual switch evaluation,
downset sizing, address arithmetic, row iteration, and the one-time depth
and Pascal initializers add only a factor of exponent zero to the existing
shared-box ledger. The bank is indexed by occurrence and two bands alone.
-/

namespace ThreeSum.SharedReportingBankCosts
open _root_.ThreeSum.SharedReportingBankCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.Filter
open _root_.ThreeSum.SharedReportingCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts
open scoped _root_.Topology

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000























noncomputable section

theorem round_extra_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.roundExtra 0 := by
  have hw := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.width_powerBound.add_same (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)
  have hpoly : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 1400*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.width n+1)^2) 0 := by
    simpa only [mul_zero,zero_add] using (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1400).mul (hw.pow 2)
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchCosts.time_powerBound.add_same hpoly).add_same (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 2808)

theorem round_overhead_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.roundOverhead 0 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.overhead_powerBound.add_same _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.round_extra_powerBound

theorem setup_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.setup 0 := by
  have hw := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.local_width_powerBound.add_same (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)
  have hpoly : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 1500*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.localWidth n+1)^2) 0 := by
    simpa only [mul_zero,zero_add] using (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1500).mul (hw.pow 2)
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchCosts.depth_powerBound.add_same hpoly).add_same (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 3300)

theorem overhead_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.overhead 0 :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.round_overhead_powerBound.add_same (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1600)).add_same _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.setup_powerBound

theorem budget_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.budget (2-_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving) := by
  have hconst : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun _ : ℕ => 1) (2-_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving) :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1).mono_exponent (by norm_num [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving])
  change _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.overhead n*(_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.boxCount n+1)) (2-_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving)
  simpa only [zero_add] using _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.overhead_powerBound.mul (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.boxes_powerBound.add_same hconst)

theorem budget_certificate : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.budget _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.budget_powerBound.mono_exponent (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.all_costs_le_raw_exponent _ (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.costLedger]))



end
end ThreeSum.SharedReportingBankCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Polynomial limits for the actual shared reporting host

The finite word, cell, and depth formulas are bounded at every input size.
The resulting `Need` includes the complete executed host, while its time
bound remains the exact shared-box budget proved separately.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.Filter
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open scoped _root_.Topology

set_option maxHeartbeats 1200000
set_option maxRecDepth 14000

noncomputable section

theorem bits_power_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 2^(_root_.ThreeSum.Scales.inputBits n)) 1 := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.identity_powerBound
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  simpa only [_root_.ThreeSum.Scales.inputBits,Nat.log2_eq_log_two] using
    Nat.pow_log_le_self 2 (by omega : n ≠ 0)

theorem magnitude_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude 2048 := by
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const (2^2048)).mul (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.bits_power_powerBound.pow 2048)
  have he : _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude = fun n => 2^2048*(2^(_root_.ThreeSum.Scales.inputBits n))^2048 := by
    funext n
    unfold _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude
    rw [show 2048*(_root_.ThreeSum.Scales.inputBits n+1)=2048+_root_.ThreeSum.Scales.inputBits n*2048 by omega,pow_add,pow_mul]
  rw [he]
  simpa only [Nat.cast_ofNat,mul_one,zero_add] using hh

















end
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

theorem total_keys_eq (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))=
      _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n := by
  have hh : 2*_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)=_root_.ThreeSum.Scales.muZero n := rfl
  have hw : 464*_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)=232*_root_.ThreeSum.Scales.muZero n := by rw [← hh]; ring
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount _root_.ThreeSum.LocalCoverBounds.outputCount
    _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.replicatedHalf _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs
  rw [mul_pow,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize_eq_length]
  congr 1
  rw [hh,hw]



variable {μ : ℕ → ℤ} {free n : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n → ℤ}
    {A B C : List ℤ} {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}



















open _root_.Filter



end ThreeSum.ThreeSumColorBudgets

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # A proved polynomial scale for the selected-color program's dimensions -/

namespace ThreeSum.EncodedColorResources
open _root_.ThreeSum.EncodedColorResources


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.Filter

set_option maxHeartbeats 2200000
set_option maxRecDepth 13000







theorem scale_bounds (n : ℕ) : 100 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧ n+1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧
    _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧ _root_.ThreeSum.EncodedColorResources.localEnvelope n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧ _root_.ThreeSum.Scales.primeWindow n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale
  omega

theorem local_bounds (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude.Bounds (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n) := by
  have hm : _root_.ThreeSum.LightLocalCoverMagnitude.magnitude (_root_.ThreeSum.EncodedColorResources.half n) ≤ _root_.ThreeSum.EncodedColorResources.localEnvelope n := by
    unfold _root_.ThreeSum.LightLocalCoverMagnitude.magnitude _root_.ThreeSum.EncodedColorResources.localEnvelope _root_.ThreeSum.LightLocalCoverInitResources.envelope
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by decide : 600000 ≤ 5000000))
  have hs := hm.trans (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.2.2.1
  have H := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude.bounds (_root_.ThreeSum.EncodedColorResources.half n)
  exact ⟨H.positive.trans hs,H.width.trans hs,H.vertices.trans hs,H.prime.trans hs,
    H.cap.trans hs,H.candidates.trans hs,H.rounds.trans hs,H.decodePower.trans hs,H.maskPower.trans hs⟩



theorem powers (n : ℕ) : 2^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.width n+1) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.EncodedColorResources.half n)^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.EncodedColorResources.half n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ∧
    2^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by
  have H := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.components n
  have hm := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.2.1
  refine ⟨H.widthPower.trans hm,H.occurrence.trans hm,H.primePower.trans hm,?_⟩
  have htwo : (2 : ℕ) ≤ 2^(464*_root_.ThreeSum.EncodedColorResources.half n)+1 := by have hh := Nat.two_pow_pos (464*_root_.ThreeSum.EncodedColorResources.half n); omega
  exact (Nat.pow_le_pow_left htwo (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)).trans (H.radixPower.trans hm)

theorem modulus_le (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by
  exact (Nat.le_mul_of_pos_right _ (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos (_root_.ThreeSum.EncodedColorResources.half n))).trans (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.powers n).2.2.1

theorem endpoint_le (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^2 := by
  have hw : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.width n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.dimensions n).1; omega
  have hh := Nat.mul_le_mul hw (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.powers n).2.2.1
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.width,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus,pow_two] using hh

theorem radix_power_le (n : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.EncodedColorResources.half n)+1)^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^2 := by
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos (_root_.ThreeSum.EncodedColorResources.half n)
  have hmod := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.modulus_le n
  calc
    _ ≤ (2*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.EncodedColorResources.half n))^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) := Nat.pow_le_pow_left (by omega) _
    _ = 2^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.EncodedColorResources.half n)^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) := mul_pow _ _ _
    _ ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n*_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := Nat.mul_le_mul (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.powers n).2.2.2 hmod
    _ = _ := by ring







theorem keyBound_le (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.keyBound (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n) ≤ 3*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^4 := by
  have hP := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.2.2.2.1
  have hL : 464*_root_.ThreeSum.EncodedColorResources.half n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by have h := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.local_bounds n).width; omega
  have hp : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.EncodedColorResources.half n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by have h := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.local_bounds n).prime; omega
  have hm := Nat.mul_le_mul (Nat.mul_le_mul hL hp) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.radix_power_le n)
  have hs4 : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^4 := Nat.le_self_pow (by decide) _
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.keyBound
  nlinarith only [hm,hP,hs4]

noncomputable section

theorem localEnvelope_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum.EncodedColorResources.localEnvelope 0 := by
  refine _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono (g := _root_.ThreeSum.Scales.localSearch 5000000) ?_ ?_
  · intro d hd
    simpa only [zero_add] using _root_.ThreeSum1960614.Machine.ThreeSum.Scales.localSearch_subpolynomial 5000000 hd
  · filter_upwards [(_root_.ThreeSum.Scales.microHalf_tendsto_atTop.comp _root_.ThreeSum.Scales.inputBits_tendsto_atTop).eventually
      (eventually_ge_atTop 1)] with n hn
    exact _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInitResources.envelope_le_search hn

theorem scale_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale 2048 := by
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.localEnvelope_powerBound.mono_exponent (by norm_num : (0 : ℝ) ≤ 2048)
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod_powerBound.mono_exponent (show _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+1/2) ≤ (2048 : ℝ) by
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E_bounds.2; unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon; linarith)
  have hy := _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.window_powerBound.mono_exponent (by norm_num : (0 : ℝ) ≤ 2048)
  have hn := _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.identity_powerBound.mono_exponent (by norm_num : (1 : ℝ) ≤ 2048)
  have hc := (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 100).mono_exponent (by norm_num : (0 : ℝ) ≤ 2048)
  exact ((((_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.magnitude_powerBound.add_same hl).add_same hp).add_same hy).add_same hn).add_same hc

end
end ThreeSum.EncodedColorResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Include the executed wanted decoder and scratch-pointer constructor

The actual physical indices have a size-only bound, independently of the
input integer magnitude. Their logarithmic decoder cost and the literal
layout power loop therefore contribute exponent zero. A fixed caller cost
is included explicitly for the remaining register loads and calls.
-/

namespace ThreeSum.SharedTraversalCosts
open _root_.ThreeSum.SharedTraversalCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000













open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open scoped _root_.Topology

noncomputable section

theorem scalar_overhead_powerBound (c : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scalarOverhead c) 0 := by
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.bits_powerBound
  have hj : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks 0 := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks_powerBound
  have hw : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n)) 0 := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.width_powerBound
  have hlog : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 8192*(_root_.ThreeSum.Scales.inputBits n+1)+3) 0 := by
    have hh : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 8192*(_root_.ThreeSum.Scales.inputBits n+1)) 0 := by
      simpa only [zero_add] using (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 8192).mul (hb.add_same (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1))
    exact hh.add_same (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 3)
  have hd : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 800*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n+1)*(8192*(_root_.ThreeSum.Scales.inputBits n+1)+3)) 0 := by
    simpa only [zero_add] using ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 800).mul (hj.add_same (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1))).mul hlog
  have hwidth : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 20*_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width (_root_.ThreeSum.SharedTraversalCosts.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.blocks n)) 0 := by
    simpa only [zero_add] using (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 20).mul hw
  exact (((hd.add_same (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 8300)).add_same hwidth).add_same
    (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 2520)).add_same (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const c)

theorem total_overhead_powerBound (c : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.totalOverhead c) 0 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.overhead_powerBound.add_same (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.scalar_overhead_powerBound c)

theorem dispatchBudget_powerBound (c k : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.dispatchBudget c k) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent := by
  have hp : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.totalOverhead c n*
      (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.initialCount _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.wantedBudget n+
        _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.activeCount (_root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.falseBudget k) n+
        _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.terminalCount (_root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.falseBudget k) n)) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent := by
    simpa only [zero_add] using (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.total_overhead_powerBound c).mul (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.traversal_counts_powerBound k)
  exact ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 30).mono_exponent
    (by exact _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.raw_exponent_nonnegative : (0 : ℝ) ≤ rawCostExponent)).add_same hp



end
end ThreeSum.SharedTraversalCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Subpolynomial scalar work in the actual selected-color preprocessing

Polynomial resource bounds are used only inside integer logarithms here.
The resulting bit-length work has exponent zero, regardless of the
polynomial degree needed to contain the machine's stored integers.
-/

namespace ThreeSum.EncodedColorTime
open _root_.ThreeSum.EncodedColorTime


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.EncodedColorResources
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open scoped _root_.Topology

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

noncomputable section

theorem sum_zero {f g : ℕ → ℕ} (hf : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f 0) (hg : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound g 0) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => f n+g n) 0 := hf.add_same hg

theorem product_zero {f g : ℕ → ℕ} (hf : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f 0) (hg : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound g 0) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => f n*g n) 0 := by simpa only [zero_add] using hf.mul hg

theorem power_zero {f : ℕ → ℕ} (hf : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f 0) (k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => f n^k) 0 := by simpa only [mul_zero] using hf.pow k

theorem log_powerBound {f : ℕ → ℕ} {a : ℝ} (hf : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => Nat.log 2 (f n+1)) 0 := by
  let k : ℕ := ⌈a+1⌉₊
  have hk : a+1 ≤ (k : ℝ) := Nat.le_ceil _
  apply _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.bitBudget_powerBound k)
  filter_upwards [hf 1 (by norm_num),eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hh := hn.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) hk)
  rw [Real.rpow_natCast] at hh
  have hfn : f n ≤ n^k := by exact_mod_cast hh
  exact (Nat.log_mono_right (b := 2) (Nat.add_le_add_right hfn 1)).trans
    ((Nat.le_succ _).trans (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.remainder_bits_le k (by omega)))

theorem clog_powerBound {f : ℕ → ℕ} {a : ℝ} (hf : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound f a) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => Nat.clog 2 (f n)) 0 := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.log_powerBound hf) (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1))
  exact Eventually.of_forall fun n => Nat.clog_le_of_le_pow
    ((Nat.le_succ (f n)).trans (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (f n+1)).le)

theorem bounded_log {f : ℕ → ℕ} (C e : ℕ)
    (hf : ∀ n, f n ≤ C*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n)^e) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => Nat.log 2 (f n+1)) 0 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.log_powerBound (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const C).mul (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_powerBound.pow e))
    (Eventually.of_forall hf))

theorem half_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum.EncodedColorResources.half 0 := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.half_powerBound

theorem blocks_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks 0 := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks_powerBound

theorem local_width_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 464*_root_.ThreeSum.EncodedColorResources.half n) 0 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 464) _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.half_powerBound

theorem width_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.width 0 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.blocks_powerBound _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.local_width_powerBound

theorem mu_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu 0 := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 2) _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.half_powerBound) _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.blocks_powerBound
  simpa only [_root_.ThreeSum.EncodedColorResources.half,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing.cutoff_eq] using hh

theorem local_product_log_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => Nat.log 2 ((464*_root_.ThreeSum.EncodedColorResources.half n)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.EncodedColorResources.half n)+1)) 0 := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.bounded_log 1 2
  intro n
  have hL : 464*_root_.ThreeSum.EncodedColorResources.half n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by have h := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.local_bounds n).width; omega
  have hP : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.EncodedColorResources.half n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale n := by have h := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.local_bounds n).prime; omega
  simpa only [one_mul,pow_two] using Nat.mul_le_mul hL hP

theorem endpoint_log_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)+1)) 0 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.bounded_log 1 2 (fun n => by simpa only [one_mul] using _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.endpoint_le n)

theorem occurrence_log_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)+1)) 0 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.bounded_log 1 1 (fun n => by simpa only [one_mul,pow_one] using (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.powers n).2.1)

theorem key_log_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.keyBound (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)+1)) 0 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.bounded_log 3 4 _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.keyBound_le

theorem moduli_log_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n+1)) 0 := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.bounded_log 2 1
  intro n
  have hp := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.scale_bounds n).2.2.2.2.1
  have hm := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.dimensions n).2.2.2.2
  simp only [pow_one]
  omega

theorem radix_log_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n+1)) 0 := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.bounded_log 2 1
  intro n
  have hm := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.dimensions n).2.2.2.2
  simp only [pow_one]
  omega

theorem input_log_powerBound (k : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => Nat.log 2 (n^k+1)) 0 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.log_powerBound (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.identity_powerBound.pow k)

end
end ThreeSum.EncodedColorTime

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact polynomial resources for the executed parameter initializer

The nineteen-cell output starts at an arbitrary destination. Scratch begins
immediately after that header; its reservation is translated only once.
-/

namespace ThreeSum.ThreeSumParameterResources
open _root_.ThreeSum.ThreeSumParameterResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.EncodedColorResources
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds

set_option maxHeartbeats 2200000
set_option maxRecDepth 14000







theorem local_envelope_le (n : ℕ) :
    _root_.ThreeSum.LocalParameterBounds.envelope (_root_.ThreeSum.LightParameterInit.half n) ≤ _root_.ThreeSum.EncodedColorResources.localEnvelope n := by
  unfold _root_.ThreeSum.LocalParameterBounds.envelope _root_.ThreeSum.EncodedColorResources.localEnvelope _root_.ThreeSum.LightLocalCoverInitResources.envelope
  apply Nat.pow_le_pow_right (by decide)
  change 2048*(_root_.ThreeSum.EncodedColorResources.half n+1)+2 ≤ 5000000*(_root_.ThreeSum.EncodedColorResources.half n+1)^2
  nlinarith only [Nat.zero_le (_root_.ThreeSum.EncodedColorResources.half n*_root_.ThreeSum.EncodedColorResources.half n)]

















noncomputable section





end







end ThreeSum.ThreeSumParameterResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact physical count scales for the selected-color preprocessing -/

namespace ThreeSum.EncodedColorTime
open _root_.ThreeSum.EncodedColorTime


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.EncodedColorResources
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales

set_option maxHeartbeats 1600000
set_option maxRecDepth 12000

noncomputable section

theorem band_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.bandSize_log_rate_shift

theorem count_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) (2*(1-_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))) := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.owner_count_powerBound
  exact Eventually.of_forall fun n => by
    have hs := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.size_le_bandCount (n := n) (le_refl n)
    have hh := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hs 2)
    exact hh.trans (Nat.le_succ _)

theorem incidence_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap (2-_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.band_powerBound.mul _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.count_powerBound
  convert hh using 1 <;> (first | rfl | ring)

theorem keys_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)) (2*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E) := by
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount_log_rate).mul
    (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs_log_ratio_tendsto)
  have he : (0 : ℝ)+2*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E=2*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon; ring
  rw [he] at hh
  simpa only [_root_.ThreeSum.EncodedColorResources.half,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks,_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.total_keys_eq] using hh

theorem wanted_rows_le (n : ℕ) :
    3*_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n*_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)/_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.wantedBudget n := by
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.size_le_bandCount (n := n) (le_refl n)
  have hcap : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n*(3*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hs 2))
  have hc := Nat.mul_le_mul_right (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n))
    (Nat.mul_le_mul_left 3 hcap)
  have he : 3*(_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n*(3*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2))*_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)=
      _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.wantedNumerator n := by
    rw [show _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)=
      _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.scheduleCount n*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n from _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.total_keys_eq n]
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.MassScales.wantedNumerator
    ring
  rw [he] at hc
  exact Nat.div_le_div_right hc

theorem wanted_rows_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n =>
      3*_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n*_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)/_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n)
      (2-_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(1/2+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds.wantedBudget_powerBound (Eventually.of_forall _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.wanted_rows_le)

theorem incidence_three_halves : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap (3/2) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.incidence_powerBound.mono_exponent (by have h := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E_bounds.1; unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon; linarith)

theorem count_one : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) 1 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.count_powerBound.mono_exponent (by have h := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E_bounds.1; unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon; linarith)

theorem keys_certificate :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent :=
  _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.keys_powerBound.mono_exponent (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.all_costs_le_raw_exponent _ (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.costLedger]))

theorem incidence_certificate : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent :=
  _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.incidence_three_halves.mono_exponent (by linarith [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.raw_exponent_lower])

theorem radix_certificate : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_log_ratio_tendsto).mono_exponent (by
    have h := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E_bounds.2
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon
    have hraw := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.raw_exponent_lower
    linarith)

theorem wanted_rows_certificate :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n =>
      3*_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n*_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)/_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n)
      _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent :=
  _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.wanted_rows_powerBound.mono_exponent (by
    have hraw := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.raw_exponent_lower
    norm_num [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon]
    linarith)

end
end ThreeSum.EncodedColorTime

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Running time of the executed occurrence-shared source banks -/

namespace ThreeSum.EncodedColorTime
open _root_.ThreeSum.EncodedColorTime


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.EncodedColorResources
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

noncomputable section

theorem retained_factor_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedProgram.factor (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)) 0 := by
  have hw := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.width_powerBound (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)
  have hj := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.blocks_powerBound (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.local_width_powerBound (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.local_product_log_powerBound (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.endpoint_log_powerBound (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)
  have h1 := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1200) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.power_zero hw 2)
  have h2 := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 300) hj) hl
  have h3 := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 600) hw
  have h4a := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 300) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.power_zero hw 2)
  have h4b := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 150) _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.local_width_powerBound)
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 464) hp)) (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 250)
  have h4 := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero h4a (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.blocks_powerBound h4b)) (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 400)
  have h5 := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 314) he
  have h6 := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 12000) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.power_zero hw 4)
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedProgram.factor,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.width] using
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero h1 h2) h3) h4) h5) h6)
      (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1122)

theorem catalog_factor_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalogProgram.factor (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)) 0 := by
  have hj := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.blocks_powerBound (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.occurrence_log_powerBound (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 2)
  exact _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.retained_factor_powerBound (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1120))
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 300) hj) hr)

theorem controls_factor_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.SourceControlCosts.factor (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)) 0 := by
  have hw := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.width_powerBound (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)
  have h1 := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1400) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.power_zero hw 2)
  have h2 := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 20) _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.blocks_powerBound
  have h3 := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 14) _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.local_product_log_powerBound
  have h4 := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 14) _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.endpoint_log_powerBound
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.SourceControlCosts.factor,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.width] using
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero h1 h2) h3) h4) (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 2044)

theorem source_factor_powerBound (k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n =>
      _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalogProgram.factor (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)*(232*_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+2)+
        2032*(Nat.log 2 (n^k+1)+Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n+1)+1)+
        _root_.ThreeSum1960614.Machine.ThreeSum.SourceControlCosts.factor (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)+5705) 0 := by
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 232) _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.mu_powerBound) (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 2)
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.input_log_powerBound k) _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.moduli_log_powerBound) (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)
  exact _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.catalog_factor_powerBound hc)
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 2032) hb)) _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.controls_factor_powerBound) (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 5705)

theorem source_time_powerBound (k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.SourceFiniteCosts.time n (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (n^k) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n))
      (1+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E-_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) := by
  have he : (0 : ℝ) ≤ 1+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E-_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift) := by
    have h := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E_bounds.1
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift
    linarith
  have hh := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.source_factor_powerBound k).mul _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.encoder_powerBound
  simp only [zero_add] at hh
  exact hh.add_same ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 4859).mono_exponent he)

theorem sources_time_powerBound (k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorSourcesCosts.time n (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (n^k) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n))
      (1+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E-_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) := by
  have he : (0 : ℝ) ≤ 1+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E-_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift) := by
    have h := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E_bounds.1
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift
    linarith
  have hJ := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 20) _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.blocks_powerBound).mono_exponent he
  have hh := ((_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.source_time_powerBound k).add_same hJ).add_same
    ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1020).mono_exponent he)
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorSourcesCosts.time_eq,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks] using hh

theorem sources_time_certificate (k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorSourcesCosts.time n (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (n^k) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n))
      _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sources_time_powerBound k).mono_exponent (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.all_costs_le_raw_exponent _ (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.costLedger]))

end
end ThreeSum.EncodedColorTime

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Charge the executed parameter initialization

The actual square-root and quotient loops are bounded by the band root and
divisor. Polynomial storage envelopes do not replace these time bounds.
-/

namespace ThreeSum.ThreeSumParameterResources
open _root_.ThreeSum.ThreeSumParameterResources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.EncodedColorResources
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.Filter
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds

set_option maxHeartbeats 1900000
set_option maxRecDepth 14000



theorem time_le_budget (n : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.time n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.timeBudget n := by
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.time_bound n
  have hl := (_root_.ThreeSum1960614.Machine.ThreeSum.LocalParameterBounds.time_bound (_root_.ThreeSum.LightParameterInit.half n)).trans (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.local_envelope_le n)
  have hg : _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.localCount n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) ≤
      1000*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n+_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n+1) := by
    simpa only [_root_.ThreeSum.LightGlobalSizes.root,_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.localCount_pow,_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.divisor,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.exponent,_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandExponent,_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot,_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks] using
      _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.time_bound (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.localCount n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)
  have hs := Nat.sqrt_le_self (_root_.ThreeSum.Scales.inputBits n)
  have he : _root_.ThreeSum.Scales.windowExponent (_root_.ThreeSum.Scales.inputBits n) ≤ _root_.ThreeSum.Scales.inputBits n+1 := by unfold _root_.ThreeSum.Scales.windowExponent; omega
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.timeBudget _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.time _root_.ThreeSum.LightNatPower.time _root_.Light.sqrtTime
  omega

noncomputable section

theorem timeBudget_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.timeBudget 1 := by
  have hsmall : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum.Scales.inputBits n+1+_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) 0 :=
    ((_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.bits_powerBound.add_same (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)).add_same
      _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.blocks_powerBound).add_same _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.mu_powerBound
  have hroot : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot 1 :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot_log_rate).mono_exponent (by
      have hh := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E_bounds.2
      unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon
      linarith)
  have hdiv : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor 1 :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor_log_rate).mono_exponent (by norm_num [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift])
  have hlocal := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.localEnvelope_powerBound.mono_exponent (by norm_num : (0 : ℝ)≤1)
  have hh := (((hsmall.mono_exponent (by norm_num : (0 : ℝ)≤1)).add_same hroot).add_same hdiv).add_same hlocal
  change _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 10000*(_root_.ThreeSum.Scales.inputBits n+1+_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n+_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n+_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n+_root_.ThreeSum.EncodedColorResources.localEnvelope n)) 1
  simpa only [zero_add] using (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 10000).mul hh

theorem time_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.time 1 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.timeBudget_powerBound (Eventually.of_forall _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.time_le_budget)





end
end ThreeSum.ThreeSumParameterResources

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Time of constructing the retained local cover and all global key rows -/

namespace ThreeSum.EncodedColorTime
open _root_.ThreeSum.EncodedColorTime


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.EncodedColorResources
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding

set_option maxHeartbeats 1600000
set_option maxRecDepth 12000

theorem local_magnitude_le (n : ℕ) :
    _root_.ThreeSum.LightLocalCoverMagnitude.magnitude (_root_.ThreeSum.EncodedColorResources.half n) ≤ _root_.ThreeSum.EncodedColorResources.localEnvelope n := by
  unfold _root_.ThreeSum.LightLocalCoverMagnitude.magnitude _root_.ThreeSum.EncodedColorResources.localEnvelope _root_.ThreeSum.LightLocalCoverInitResources.envelope
  exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by decide : 600000 ≤ 5000000))

noncomputable section

theorem local_schedule_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize (_root_.ThreeSum.EncodedColorResources.half n)) 0 := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.localEnvelope_powerBound
  exact Eventually.of_forall fun n => by
    have h := (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude.bounds (_root_.ThreeSum.EncodedColorResources.half n)).rounds.trans (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.local_magnitude_le n)
    omega

theorem local_layer_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum.LocalCoverBounds.outputCount (464*_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum.EncodedColorResources.half n)) 0 := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.localEnvelope_powerBound
  exact Eventually.of_forall fun n => by
    have h := (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude.bounds (_root_.ThreeSum.EncodedColorResources.half n)).maskPower.trans (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.local_magnitude_le n)
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_succ (464*_root_.ThreeSum.EncodedColorResources.half n))
    exact (Nat.choose_le_two_pow _ _).trans (hp.trans (by omega))

theorem local_cover_time_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.time (_root_.ThreeSum.EncodedColorResources.half n)) 0 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.localEnvelope_powerBound (Eventually.of_forall fun n =>
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInitResources.time_bound (_root_.ThreeSum.EncodedColorResources.half n))

theorem global_keys_time_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.time (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)) (2*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E) := by
  have he : (0 : ℝ) ≤ 2*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E := by
    have h := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E_bounds.1
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon
    linarith
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.local_width_powerBound (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)
  have hq := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.local_layer_powerBound (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.local_schedule_powerBound (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)
  have hlocal := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 2000) hl) hq) hs
  have hj := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.blocks_powerBound (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)
  have hg := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.keys_powerBound.add_same ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1).mono_exponent he)
  have hglobal : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 300*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n+1)*
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount (_root_.ThreeSum.EncodedColorResources.half n)^(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)+1)) (2*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E) := by
    simpa only [zero_add,_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys] using (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 300) hj).mul hg
  exact _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono (((hlocal.mono_exponent he).add_same hglobal).add_same
    ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 200).mono_exponent he))
    (Eventually.of_forall fun n => _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.time_bound (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n))

theorem cover_time_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.time (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)) (2*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E) := by
  have he : (0 : ℝ) ≤ 2*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E := by
    have h := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E_bounds.1
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon
    linarith
  exact ((_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.local_cover_time_powerBound.mono_exponent he).add_same _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.global_keys_time_powerBound).add_same
    ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 200).mono_exponent he)

theorem cover_time_certificate :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.time (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent :=
  _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.cover_time_powerBound.mono_exponent (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.all_costs_le_raw_exponent _ (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.costLedger]))

end
end ThreeSum.EncodedColorTime

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Time of the actual color extraction, normalization and incidence catalog -/

namespace ThreeSum.EncodedColorTime
open _root_.ThreeSum.EncodedColorTime


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.EncodedColorResources
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

noncomputable section

theorem band_width_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum.ColorBandBounds.width n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) 0 := by
  have hs : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum.BandPartition.size n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) 1 :=
    _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.identity_powerBound (Eventually.of_forall fun n => _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le n _)
  exact _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.clog_powerBound (((hs.add_same hs).add_same hs).add_same
    ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 1)))

theorem band_time_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum.ColorBandBounds.time n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) 1 := by
  have hn := _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.identity_powerBound.add_same ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 1))
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.clog_powerBound _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.identity_powerBound) (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)
  have hw := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.band_width_powerBound (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)
  have hR := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.count_one.add_same _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.identity_powerBound).add_same
    ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 1))
  have h1 : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 2100*(n+1)*(Nat.clog 2 n+1)) 1 := by
    simpa only [zero_add,add_zero] using ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 2100).mul hn).mul hl
  have h2 : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 1000*(_root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)+n+1)*
      (_root_.ThreeSum.ColorBandBounds.width n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)+1)) 1 := by
    simpa only [zero_add,add_zero] using ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1000).mul hR).mul hw
  exact (h1.add_same h2).add_same ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 400).mono_exponent (by norm_num : (0 : ℝ) ≤ 1))

theorem raw_catalog_time_le (n : ℕ) :
    _root_.ThreeSum.LightBandRawAColor.catalogTime n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) ≤ 9000*(3*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2+1)*(_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n+1) := by
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.size_le_bandCount (n := n) (le_refl n)
  have hc := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hs 2)
  have hb : _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2 := Nat.le_self_pow (by decide) _
  have hsum : _root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)+3*_root_.ThreeSum.BandPartition.size n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)+1 ≤
      3*(3*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2+1) := by
    unfold _root_.ThreeSum.ColorBandBounds.count
    omega
  have hh := Nat.mul_le_mul_right (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n+1) (Nat.mul_le_mul_left 3000 hsum)
  have he : 3000*(3*(3*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2+1))=9000*(3*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2+1) := by omega
  rw [he] at hh
  exact hh

theorem raw_catalog_time_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum.LightBandRawAColor.catalogTime n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) (2-_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)) := by
  have he : (0 : ℝ) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift) := by
    have h := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E_bounds.1
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon
    linarith
  have hg := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.band_powerBound.add_same ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1).mono_exponent he)
  have hh := ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 9000).mul _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.owner_count_powerBound).mul hg
  have heq : (0 : ℝ)+2*(1-_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift))+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)=2-_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift) := by ring
  rw [heq] at hh
  exact _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono hh (Eventually.of_forall _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.raw_catalog_time_le)

theorem color_bands_time_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum.LightBandRawAColor.time (_root_.ThreeSum.Scales.inputBits n+1) n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) (3/2) := by
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.bits_powerBound (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1))
    (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)
  have hn := _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.identity_powerBound.add_same ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 1))
  have hlin : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 1200*(_root_.ThreeSum.Scales.inputBits n+1+1)*(n+1)) 1 := by
    simpa only [zero_add] using ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1200).mul hb).mul hn
  have h1 := hlin.mono_exponent (by norm_num : (1 : ℝ) ≤ 3/2)
  have h2 := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.band_time_powerBound.mono_exponent (by norm_num : (1 : ℝ) ≤ 3/2)
  have h3 := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.raw_catalog_time_powerBound.mono_exponent (show 2-_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift) ≤ (3/2 : ℝ) by
    have h := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E_bounds.1; unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon; linarith)
  have h4 := (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 600).mono_exponent (by norm_num : (0 : ℝ) ≤ 3/2)
  exact _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono (((h1.add_same h2).add_same h3).add_same h4)
    (Eventually.of_forall fun n => _root_.ThreeSum1960614.Machine.ThreeSum.LightBandRawAColor.time_bound (_root_.ThreeSum.Scales.inputBits n+1) n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n))

theorem normalized_layout_time_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum.LightEncodedColorLayout.time n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) 1 := by
  have hh : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 20*n+1040) 1 := by
    have h := (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 20).mul _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.identity_powerBound
    simp only [zero_add] at h
    exact h.add_same ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1040).mono_exponent (by norm_num : (0 : ℝ) ≤ 1))
  apply _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono hh
  exact Eventually.of_forall fun n => by
    have h := _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.time_bound (n-1) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
    unfold _root_.ThreeSum.LightEncodedColorLayout.time
    omega

theorem normalize_time_powerBound : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorNormalize.time (3/2) :=
  (((_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.normalized_layout_time_powerBound.mono_exponent (by norm_num : (1 : ℝ) ≤ 3/2)).add_same
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.color_bands_time_powerBound).add_same
      ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1200).mono_exponent (by norm_num : (0 : ℝ) ≤ 3/2)))

theorem normalize_time_certificate : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorNormalize.time _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent :=
  _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.normalize_time_powerBound.mono_exponent (by linarith [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.raw_exponent_lower])

end
end ThreeSum.EncodedColorTime

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact outer-driver time from the concrete per-color certificate -/

namespace ThreeSum.ThreeSumColorDriverCosts
open _root_.ThreeSum.ThreeSumColorDriverCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds

set_option maxHeartbeats 1800000

noncomputable section

theorem time_powerBound {T : ℕ→ℕ} {a : ℝ} (hT : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound T a) (ha : 1≤a) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.time (T n) n) a := by
  have hzero : 0≤a := by linarith
  have hparams := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumParameterResources.time_powerBound.mono_exponent ha
  have hscan := _root_.ThreeSum1960614.Machine.ThreeSum.LightColorScanCosts.time_powerBound hT hzero
  change _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.time n+_root_.ThreeSum.LightColorScanHost.time (T n) n+500) a
  exact (hparams.add_same hscan).add_same ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 500).mono_exponent hzero)

theorem time_certificate {T : ℕ→ℕ} (hT : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound T _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumFastDriver.time (T n) n) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverCosts.time_powerBound hT (by linarith [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.raw_exponent_lower])





end
end ThreeSum.ThreeSumColorDriverCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Time of the actual balanced wanted-record construction

The emitted-record term retains the proved division by the dense modulus.
The remaining terms scan the original A incidences and global key rows,
construct histograms, and execute the verified correlation/minimum routine.
-/

namespace ThreeSum.EncodedColorTime
open _root_.ThreeSum.EncodedColorTime


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.EncodedColorResources
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum.ModuloCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.ModuloCosts

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000

theorem original_offset_time_le (p NL NR U : ℕ) :
    _root_.ThreeSum.LightOriginalOffset.time p NL NR U ≤
      3000*_root_.ThreeSum.ModuloCosts.roundedPower p+131*(NL+NR)*(Nat.log 2 (U+1)+1)+642 := by
  have ht := _root_.ThreeSum.LightOriginalOffset.time_bound p NL NR U
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.ModuloCosts.capacity_le_roundedPower p
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.ModuloCosts.log_le_roundedPower p
  have hk : _root_.ThreeSum.LightKaratsuba.time (Nat.clog 2 p) ≤ 2530*_root_.ThreeSum.ModuloCosts.roundedPower p := _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.time_le _
  omega

noncomputable section

theorem const_certificate (c : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun _ => c) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const c).mono_exponent (by linarith [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.raw_exponent_lower])

theorem raw_keys_time_powerBound (k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum.LightRawAKeys.time (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n) (n^k)) (3/2) := by
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.incidence_three_halves.add_same
    ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 3/2))
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.input_log_powerBound k) (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)
  have hh : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 220*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n+1)*
      (Nat.log 2 (n^k+1)+1)) (3/2) := by
    simpa only [zero_add,add_zero] using ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 220).mul hc).mul hl
  exact _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono hh (Eventually.of_forall fun n => _root_.ThreeSum1960614.Machine.ThreeSum.LightRawAKeys.time_bound _ _)

theorem rounded_radix_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum.ModuloCosts.roundedPower (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n)) ((8/5)*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon*(_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E+1/2))) := by
  apply _root_.ThreeSum.ArithmeticStageBounds.powerBound_of_fifth (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.of_rate _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_log_ratio_tendsto)
  intro n
  simpa only [show (2 : ℕ)^8=256 by norm_num] using _root_.ThreeSum.ModuloCosts.roundedPower_fifth (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)

theorem rounded_radix_certificate :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum.ModuloCosts.roundedPower (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n)) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent :=
  _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.rounded_radix_powerBound.mono_exponent (by
    have h := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E_bounds.2
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon
    have hraw := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.raw_exponent_lower
    linarith)

theorem left_keys_certificate :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 3*_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent := by
  simpa only [zero_add] using (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 3).mul _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.incidence_certificate

theorem original_offset_time_certificate :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum.LightOriginalOffset.time (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (3*_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n)
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n))
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.keyBound (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n))) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent := by
  have hcount := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.left_keys_certificate.add_same _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.keys_certificate
  have hlog := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.key_log_powerBound (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)
  have h1 : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 3000*_root_.ThreeSum.ModuloCosts.roundedPower (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n)) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent := by
    simpa only [zero_add] using (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 3000).mul _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.rounded_radix_certificate
  have h2 : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => 131*(3*_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n+
      _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n))*
      (Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.keyBound (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)+1)+1))
      _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent := by
    simpa only [zero_add,add_zero] using ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 131).mul hcount).mul hlog
  exact _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono ((h1.add_same h2).add_same (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.const_certificate 642))
    (Eventually.of_forall fun n => _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.original_offset_time_le _ _ _ _)

theorem wanted_scan_time_certificate :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n =>
      2000*(3*_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n+_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)+
        _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n+3*_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n*
          _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)/_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n+1)*
        (Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.keyBound (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)+1)+
          Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n+_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n+1)+1)) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent := by
  have hc := (((_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.left_keys_certificate.add_same _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.keys_certificate).add_same _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.radix_certificate).add_same
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.wanted_rows_certificate).add_same (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.const_certificate 1)
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.key_log_powerBound _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.radix_log_powerBound) (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1)
  simpa only [zero_add,add_zero] using ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 2000).mul hc).mul hl

theorem wanted_time_certificate (k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.time (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)
      (n^k) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n)) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent := by
  have hraw := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.raw_keys_time_powerBound k).mono_exponent
    (show (3/2 : ℝ) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent by linarith [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.raw_exponent_lower])
  exact (((_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.cover_time_certificate.add_same hraw).add_same _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.original_offset_time_certificate).add_same
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.wanted_scan_time_certificate).add_same (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.const_certificate 400)

end
end ThreeSum.EncodedColorTime

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The executed selected-color preprocessing fits the final time exponent

This charges the actual fixed256 program's complete time expression:
normalization and incidence construction, common-prime selection, local
cover and global keys, balanced wanted rows, shared source banks and the
retained result-header computation. Reporting and the outer color loop
remain separate composition obligations.
-/

namespace ThreeSum.EncodedColorTime
open _root_.ThreeSum.EncodedColorTime


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.EncodedColorResources
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open scoped _root_.Topology

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000



noncomputable section

theorem prime_time_certificate (k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum.LightEncodedColorPrime.time (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) n n n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)
      (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.Scales.primeWindow n) (n^k)) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono ((_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.timeBudget_certificate k).add_same (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.const_certificate 1160))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeCosts.time_le_budget (nA := n) (nB := n) (nC := n)
    (n := n) k (by omega) le_rfl le_rfl le_rfl

theorem prime_host_time_certificate (k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeHost.inputTime n (n^k)) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent := by
  change _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorNormalize.time n+
    _root_.ThreeSum.LightEncodedColorPrime.time (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) n n n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.Scales.primeWindow n) (n^k)+600) _
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.normalize_time_certificate.add_same (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.prime_time_certificate k)).add_same (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.const_certificate 600)

theorem stage_time_certificate (k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.time n (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (n^k)
      (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n)) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent := by
  change _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedCosts.time (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.EncodedColorResources.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)
    (n^k) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n)+_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorSourcesCosts.time n (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (n^k) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n)+400) _
  exact ((_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.wanted_time_certificate k).add_same (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sources_time_certificate k)).add_same (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.const_certificate 400)

theorem wanted_header_time_powerBound :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum.LightEncodedColorWantedHeader.time (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)) 0 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.sum_zero (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.product_zero (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 100) _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.blocks_powerBound) (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1000)

theorem pipeline_time_powerBound (k : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.preprocessingTime k) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent := by
  change _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorPrimeHost.inputTime n (n^k)+
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.time n (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (n^k) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorStageCosts.incidenceCap n)+
    _root_.ThreeSum.LightEncodedColorWantedHeader.time (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorResources.blocks n)+1600) _
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.wanted_header_time_powerBound.mono_exponent (show (0 : ℝ) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent by
    linarith [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.raw_exponent_lower])
  exact (((_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.prime_host_time_certificate k).add_same (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.stage_time_certificate k)).add_same hh).add_same
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.const_certificate 1600)





end
end ThreeSum.EncodedColorTime

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual time of the source, shared reporting and dense prefixProgram -/

namespace ThreeSum.EncodedColorReportingCosts
open _root_.ThreeSum.EncodedColorReportingCosts


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open scoped _root_.Topology

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000









theorem dense_time_le_budget {n : ℕ} (k : ℕ) (hn : 0 < n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.time n (n^k) (_root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n)) ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetupCosts.timeBudget k n+1600 := by
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandCosts.size_le_bandCount (n := n) (le_refl n)
  have hc : _root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) ≤ 3*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2 :=
    Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hs 2)
  exact Nat.add_le_add_right (_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetupCosts.time_le_budget k hn hc) 1600

noncomputable section

theorem bank_time_certificate :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupBank.time _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent := by
  change _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.budget n+400) _
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankCosts.budget_certificate.add_same (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.const_certificate 400)

theorem dense_time_certificate (k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.time n (n^k)
      (_root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n))) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.powerBound_mono ((_root_.ThreeSum1960614.Machine.ThreeSum.LightDenseSetupCosts.timeBudget_certificate k).add_same
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.const_certificate 1600))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingCosts.dense_time_le_budget k (by omega)

theorem setup_time_certificate (k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingCosts.setupTime n (n^k)) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent := by
  change _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupBank.time n+
    _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumReportingSetupDense.time n (n^k) (_root_.ThreeSum.ColorBandBounds.count n (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n))+200) _
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingCosts.bank_time_certificate.add_same (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingCosts.dense_time_certificate k)).add_same
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.const_certificate 200)

theorem time_powerBound (k : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingCosts.preprocessingTime k) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent := by
  change _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (fun n => _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.preprocessingTime k n+_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingCosts.setupTime n (n^k)+1000) _
  exact ((_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.pipeline_time_powerBound k).add_same (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingCosts.setup_time_certificate k)).add_same
    (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorTime.const_certificate 1000)





end
end ThreeSum.EncodedColorReportingCosts

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









noncomputable section

theorem color_budget_powerBound (k : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.colorBudget k) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent := by
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorReportingCosts.time_powerBound k
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.dispatchBudget_powerBound 4800 k
  exact (hp.add_same hr).add_same ((_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 5000).mono_exponent
    (by exact _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.raw_exponent_nonnegative))



end
end ThreeSum.SharedTraversalCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The exact hybrid cost along every fixed input-magnitude exponent

The exceptional-size and excessive-magnitude branches use the original
triple scan. Once the size reaches the fixed cutoff, every bound at most
n^κ selects the same fast cost. The scalar exponentiation and fixed caller
cost fit within the proved gap between the certificate and target exponents.
-/

namespace ThreeSum.ThreeSumHybridCosts
open _root_.ThreeSum.ThreeSumHybridCosts


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.Filter

set_option maxHeartbeats 1200000
set_option maxRecDepth 12000





theorem time_of_large {κ cutoff n U : ℕ} (hn : cutoff≤n) (hU : U≤n^κ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.time κ cutoff n U=_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.fastTime κ n := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.time,_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.fastTime,if_neg (not_or_intro (Nat.not_lt.mpr hn) (Nat.not_lt.mpr hU))]

noncomputable section

theorem fastTime_powerBound (κ : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.fastTime κ) _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent := by
  have hfast := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorDriverCosts.time_certificate
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.color_budget_powerBound κ)
  have hp := (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const (_root_.ThreeSum.LightNatPower.time κ)).mono_exponent
    (show (0 : ℝ)≤_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent by linarith [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.raw_exponent_lower])
  have hc := (_root_.ThreeSum1960614.Machine.ThreeSum.StageBounds.PowerBound.const 1000).mono_exponent
    (show (0 : ℝ)≤_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent by linarith [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.raw_exponent_lower])
  exact (hfast.add_same hp).add_same hc



theorem fastTime_eventually_at (κ : ℕ) {r : ℝ}
    (hgap : _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent < r) :
    ∀ᶠ n : ℕ in atTop, (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.fastTime κ n : ℝ) ≤ (n : ℝ)^r := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.fastTime_powerBound κ (r-_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent) (sub_pos.mpr hgap)
  simpa only [add_sub_cancel] using hh





theorem timeUpTo_le_fastTime {κ cutoff n : ℕ} {u : ℝ}
    (hn : cutoff≤n) (hu : u≤(n : ℝ)^(κ : ℝ)) :
    _root_.Light.timeUpTo (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.time κ cutoff) n u≤(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.fastTime κ n : ℝ) := by
  apply _root_.ThreeSum1960614.Machine.Light.timeUpTo_le
  intro U hU
  have hp : 0≤(n : ℝ)^(κ : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hU' : (U : ℝ)≤(n : ℝ)^(κ : ℝ) := hU.trans (max_le hu hp)
  have hUnat : U≤n^κ := by
    rw [Real.rpow_natCast] at hU'
    exact_mod_cast hU'
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.time_of_large hn hUnat]

/-- The finite supremum over all input bounds is exactly the fast branch. -/
theorem timeUpTo_eq_fastTime {κ cutoff n : ℕ} (hn : cutoff≤n) :
    _root_.Light.timeUpTo (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.time κ cutoff) n ((n : ℝ)^(κ : ℝ))=(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.fastTime κ n : ℝ) := by
  apply le_antisymm (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.timeUpTo_le_fastTime hn le_rfl)
  have hzero : (0 : ℝ)≤(n : ℝ)^(κ : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hh := _root_.ThreeSum1960614.Machine.Light.le_timeUpTo (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.time κ cutoff) n (U := 0) (u := (n : ℝ)^(κ : ℝ))
    (by simpa only [Nat.cast_zero] using hzero)
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.time_of_large hn (Nat.zero_le (n^κ))] using hh

theorem timeUpTo_eventually_at (κ cutoff : ℕ) {r : ℝ}
    (hgap : _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent < r) :
    ∀ᶠ n : ℕ in atTop,
      _root_.Light.timeUpTo (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.time κ cutoff) n ((n : ℝ)^(κ : ℝ)) ≤ (n : ℝ)^r := by
  filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.fastTime_eventually_at κ hgap,eventually_ge_atTop cutoff] with n ht hn
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.timeUpTo_eq_fastTime hn] using ht





end
end ThreeSum.ThreeSumHybridCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The complete543-procedure original-input solver

For each fixed magnitude exponent, the cutoff is chosen from the proved
uniform parameter conditions. The program tests that cutoff, computes the
integer power, and uses the exact original-triple fallback whenever needed.
Every branch returns the original distinct-position decision and preserves
all memory before the supplied free address.
-/

namespace ThreeSum.LightThreeSumHybrid
open _root_.ThreeSum.LightThreeSumHybrid


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSumApsp.Spec
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.Spec

set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

noncomputable section













theorem poly_need (κ : ℕ) : _root_.ThreeSum1960614.Machine.Light.PolyNeed (_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybrid.need κ) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumFastResourcesHybrid.poly_need κ (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.cutoff κ)



end
end ThreeSum.LightThreeSumHybrid

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Transfer the verified hybrid solver to the exact end-statement model

The premises below require an actual light-language solver of s3Task with
the frozen hybrid cost and a polynomial resource requirement. The existing
compiler realization supplies the word-RAM program. These interfaces do
not supply or assume away the executable solver obligation.
-/

namespace ThreeSum.ThreeSumHybridEndBridge
open _root_.ThreeSum.ThreeSumHybridEndBridge


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

noncomputable section

theorem realized_of_solves {κ cutoff : ℕ} {P : _root_.ThreeSum1960614.Machine.Light.Program} {p : ℕ}
    {need : ℕ→ℕ→_root_.ThreeSum1960614.Machine.Light.Need}
    (hs : _root_.ThreeSum1960614.Machine.Light.Solves _root_.ThreeSum1960614.Machine.Light.s3Task P p (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.time κ cutoff) need)
    (hp : _root_.ThreeSum1960614.Machine.Light.PolyNeed need) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Realized _root_.EndStatement.ThreeSum
      (_root_.Light.timeUpTo (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.time κ cutoff)) :=
  _root_.ThreeSum1960614.Machine.Light.Sec3.realized_threeSum _ (hs.solvedIn hp)



theorem solvedAt_of_solves_at {κ cutoff : ℕ} {P : _root_.ThreeSum1960614.Machine.Light.Program} {p : ℕ}
    {need : ℕ→ℕ→_root_.ThreeSum1960614.Machine.Light.Need} {r : ℝ}
    (hgap : _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent < r)
    (hs : _root_.ThreeSum1960614.Machine.Light.Solves _root_.ThreeSum1960614.Machine.Light.s3Task P p (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.time κ cutoff) need)
    (hp : _root_.ThreeSum1960614.Machine.Light.PolyNeed need) :
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.SolvedInTimeAt _root_.EndStatement.ThreeSum κ r 0 := by
  apply _root_.ThreeSum1960614.Machine.ThreeSumApsp.FromClaims.solvedAt_of_realized
    (_root_.Light.timeUpTo (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.time κ cutoff)) κ (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridEndBridge.realized_of_solves hs hp) (C := 1)
  simpa only [pow_zero,mul_one,one_mul] using
    _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.timeUpTo_eventually_at κ cutoff hgap

theorem endStatement_of_solvers_at {r : ℚ} (hr : 0 < r)
    (hgap : _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent < (r : ℝ))
    (h : ∀ κ : ℕ, ∃ (cutoff : ℕ) (P : _root_.ThreeSum1960614.Machine.Light.Program) (p : ℕ) (need : ℕ→ℕ→_root_.ThreeSum1960614.Machine.Light.Need),
      _root_.ThreeSum1960614.Machine.Light.Solves _root_.ThreeSum1960614.Machine.Light.s3Task P p (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridCosts.time κ cutoff) need ∧ _root_.ThreeSum1960614.Machine.Light.PolyNeed need) :
    _root_.EndStatement.ThreeSum.SolvedInTime r := by
  have hall : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.SolvedInTime _root_.EndStatement.ThreeSum (r : ℝ) 0 := by
    intro κ
    obtain ⟨cutoff,P,p,need,hs,hp⟩ := h κ
    exact _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridEndBridge.solvedAt_of_solves_at hgap hs hp
  exact hall.endStatement rfl hr.le



end
end ThreeSum.ThreeSumHybridEndBridge

end ThreeSum1960614.Machine

section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.ThreeSum1960614
open _root_.ThreeSum1960614.Machine.ThreeSum1960614

section

/-- The unchanged exact word-RAM goal for every strict rational ledger bound. -/
theorem ThreeSum1960614.costs_solve_3sum__implementation_09e247a89a (r : ℚ) (hr : 0 < r)
    (hcost : ∀ z ∈ _root_.ThreeSum1960614.costs, z < (r : ℝ)) : _root_.EndStatement.ThreeSum.SolvedInTime r := by
  have hpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hgap : _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.rawCostExponent < (r : ℝ) :=
    _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.raw_exponent_lt_of_costs_lt hpos
      (by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.actual_costLedger_eq] using hcost)
  apply _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumHybridEndBridge.endStatement_of_solvers_at hr hgap
  intro κ
  exact ⟨_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostConditions.cutoff κ,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybrid.program κ,542,_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybrid.need κ,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybrid.solves κ,_root_.ThreeSum1960614.Machine.ThreeSum.LightThreeSumHybrid.poly_need κ⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.costs_solve_3sum__implementation_09e247a89a) := (@ThreeSum1960614.costs_solve_3sum__implementation_09e247a89a)

#print axioms solution
