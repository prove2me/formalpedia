-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScanStored.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:10:12.629837+00:00
-- url     : https://prove2.me/submissions/c804b9a9-32b0-45a7-9dd0-93420c8fad92

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
import Theorems.Thm_ThreeSum_DenseGuardWanted_pair_indices_injective
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorPipelineData_Stored_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorWantedConsumerData_incidence_length_le_magnitude
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_EncodedColorWantedConsumerData_persistent_ends
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingWantedDispatchStored_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingWantedScan_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankHeader_Stored_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_output_count_le_magnitude
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_wanted_representation_cap_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_WantedRecordOrder_label_injective
import Theorems.Thm_ThreeSum_BandRawA_mem_aIndices_iff_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_allProducts
import Theorems.Thm_ThreeSum_BandRawA_mem_row
import Theorems.Thm_ThreeSum_LocalHashMoments_hitCount_cap
import Theorems.Thm_ThreeSum_Radix_representations_card_le

local instance platformRadixNonzero_168784fcb3 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Filter
end Filter
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
namespace ThreeSum.EncodedColorWantedConsumerData
end ThreeSum.EncodedColorWantedConsumerData
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightReportingWantedScan
end ThreeSum.LightReportingWantedScan
namespace ThreeSum.LightReportingWantedScanStored
end ThreeSum.LightReportingWantedScanStored
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostWantedConsumerData
end ThreeSum.ReportingHostWantedConsumerData
namespace ThreeSum.ReportingHostWantedDecision
end ThreeSum.ReportingHostWantedDecision
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
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.ThreeSumColorBudgets
end ThreeSum.ThreeSumColorBudgets
namespace ThreeSum.ThreeSumReportingSetupData
end ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum.WantedRecordOrder
end ThreeSum.WantedRecordOrder
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
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
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
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightClassFilter
end ThreeSum1960614.Machine.ThreeSum.LightClassFilter
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScan
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScan
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScanStored
end ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScanStored
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
end ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
end ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedDecision
end ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedDecision
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
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets
end ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
end ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData
namespace ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
end ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData
namespace ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder
end ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

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
# Regions of the memory, and the cells that a step leaves alone

A region is given by its first address `a` and its number `n` of cells.  `Inside a n b` says that
the cell `b` lies in it, `Outside a n b` that it does not, and `Apart a n a' n'` that two regions do
not meet.  `InOrder top [(a, n), (a', n'), …]` says that the listed regions lie one behind the other
and end at or below `top`.  All of these abbreviate linear inequalities.

`SameOn K μ μ'` says that the memory `μ'` agrees with `μ` on every cell that satisfies `K`.  It is
the one notion of "these cells are unchanged": a routine promises `SameOn K μ μ'` for the cells
`K` that it leaves alone.  (It is `Set.EqOn μ' μ {b | K b}`, stated with a predicate: the conditions
`K b` that occur are linear inequalities between addresses and are used as such.)  The usual choices
of `K` have names.

* `SameOutside μ μ' a n`: all cells outside one region; `SameOutside2` and `SameOutside3`: all cells
  outside two or three regions.
* `Kept μ μ' fr`: all cells below the free pointer `fr`.
* `KeptBut μ μ' fr out len`: all cells below `fr` outside the region of an output.

## How a fact is carried from one memory to a later one

A predicate `X` about a memory has one lemma of the name `X.keep` and of the form

  `theorem X.keep (h : X μ …) (hs : SameOn K μ μ' := by light_keep) : X μ' …`

where `K` describes the cells that `X` reads; `Seg.keep` is the model.  The argument `hs` has a
default proof.  So `h.keep`, with no argument, stands for "`h` still holds in the memory that is
asked for here".  The default proof `light_keep` uses every hypothesis of the form `SameOn _ ν ν'`
in the context, that is, the promises of the steps that were taken since `h` was obtained, and the
inequalities in the context that say where the regions lie.  In the proofs a promise is named when
the step is taken, as `same₂` in `rintro _ μ₂ ⟨sY, same₂⟩`.

`wrote μ dst f j` is the memory `μ` after a loop has written `f 0`, …, `f (j - 1)` to the cells from
`dst`.
-/

@[expose] public section

namespace Light
open _root_.Light


/-! ## Regions -/









/-! ## Memories that agree on some cells -/













variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}



theorem SameOn.refl : _root_.ThreeSum1960614.Machine.Light.SameOn K μ μ := fun _ _ => rfl

theorem SameOn.trans (h₁ : _root_.ThreeSum1960614.Machine.Light.SameOn K μ μ') (h₂ : _root_.ThreeSum1960614.Machine.Light.SameOn K μ' μ'') : _root_.ThreeSum1960614.Machine.Light.SameOn K μ μ'' :=
  fun b hb => (h₂ b hb).trans (h₁ b hb)







/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}















/-! ## The tactics -/











end Light

end

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



/-! ## Tasks and solvers -/





















/-! ## Hosts -/





/-! ## Tasks with a list of parameters -/











end Light

end

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









theorem mem_rawOn {h J : ℕ} {P d : ℤ} {T : Finset (_root_.ThreeSum.RawIncidences.Original α β γ)}
    {a : α → ℤ} {b : β → ℤ} {c : γ → ℤ} {r : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ} :
    r ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P d T a b c ↔
      r.1 ∈ T ∧ r.2 ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses h J P d (a r.1.1) (b r.1.2.1) (c r.1.2.2) :=
  Finset.mem_sigma













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







end ThreeSum.DenseGuard

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





end Mass

end ThreeSum.ReportingHostWantedLayout

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



section Actual

variable {μ : ℕ→ℤ} {f : ℕ→ℤ} {n g free M P h J : ℕ}
  {rs : List _root_.ThreeSum.BandCandidateRows.Record} {shift : ℤ}
  (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output μ free M (_root_.ThreeSum.LightGuardedWanted.left P (_root_.ThreeSum.BandRawA.values f (_root_.ThreeSum.BandRawA.items n g rs)))
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right h J) (3*(_root_.ThreeSum.BandRawA.values f (_root_.ThreeSum.BandRawA.items n g rs)).length)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) shift)



theorem wantedAt_injective : Function.Injective (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt H) :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.transport_injective (_root_.ThreeSum.ReportingHostWantedPhysical.incidenceIndices f n g rs)).comp (_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardWanted.labelAt_injective H)

theorem wantedAt_position (slot : Fin (μ free).toNat) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt H slot).1.val=
      _root_.ThreeSum.DenseGuardWanted.leftIndex μ free (3*(_root_.ThreeSum.BandRawA.items n g rs).length)
        (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) M slot.val%(_root_.ThreeSum.BandRawA.items n g rs).length := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.transport,_root_.ThreeSum.ReportingHostWantedPhysical.incidenceIndices,_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardWanted.labelAt,
    _root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder.label,_root_.ThreeSum.BandRawA.values_length,Equiv.coe_fn_mk]



theorem wantedAt_output (slot : Fin (μ free).toNat) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt H slot).2.2=_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeOriginal.output h J
      (_root_.ThreeSum.DenseGuardWanted.rightIndex μ free (3*(_root_.ThreeSum.BandRawA.items n g rs).length)
        (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys h J) M slot.val) := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.transport,_root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardWanted.labelAt,_root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordOrder.label,_root_.ThreeSum.BandRawA.values_length]



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

theorem prefix_mass_le_card (fB fC : ℕ→ℤ) (NB NC k : ℕ) (hk : k≤(μ free).toNat) :
    _root_.ThreeSum.SharedTraversalCosts.prefixMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.slotMass H fB fC NB NC) k≤
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.globalItems h J n NB NC g P rs fA fB fC shift).card := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.prefix_mass_eq H fB fC NB NC k hk]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.DenseGuard.mass_le_raw_card _ _ (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.prefix_nodup H k)



end Actual

end ThreeSum.ReportingHostWantedPrefix

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















theorem wanted_mass_bound_le {n N NB NC : ℕ}
    (hN : N≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    _root_.ThreeSum.ReportingHostWantedLayout.massBound N NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^7 := by
  have hb := hB.trans (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.input_le_magnitude n)
  have hc := hC.trans (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.input_le_magnitude n)
  have hh := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hN hb) hc)
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_representation_cap_le n)
  calc
    _ ≤ ((3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3)*_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)*_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^2 := hh
    _ = _ := by ring





end ThreeSum.SharedReportingBankResourceBounds

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









theorem incidence_length_eq (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).N=
      (_root_.ThreeSum.BandRawA.items A.length (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.records n A B C hsA hsB hsC)).length :=
  _root_.ThreeSum.BandRawA.values_length ..









theorem count_le_product (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC≤3*(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).N*
      _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) := by
  have hh := H.countBound
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count_read H,Int.toNat_natCast] at hh
  exact (Nat.le_mul_of_pos_left _ (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)).trans hh





end ThreeSum.EncodedColorWantedConsumerData

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







end Actual

end ThreeSum.ReportingHostWantedDecision

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

theorem retained_of_keptBut
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (HQ : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.Catalog μ free n A B C hsA hsB hsC)
    (K : _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).layoutHeader
      (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter 1) :
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored ν free n color x A B C hsA hsB hsC ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.Catalog ν free n A B C hsA hsB hsC :=
  _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.retained_of_kept H HQ (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.kept_counter K)

theorem metadata_reads_of_keptBut
    (K : _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).layoutHeader
      (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter 1) :
    let ctr := (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter
    ν (ctr+1)=μ (ctr+1) ∧ ν (ctr+2)=μ (ctr+2) ∧ ν (ctr+3)=μ (ctr+3) := by
  have he : (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).layoutHeader=
      (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter+4 := rfl
  exact ⟨K _ ⟨by omega,Or.inr (by omega)⟩,
    K _ ⟨by omega,Or.inr (by omega)⟩,K _ ⟨by omega,Or.inr (by omega)⟩⟩

theorem DenseMetadata.of_keptBut {cap score : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.DenseMetadata μ (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter cap score)
    (K : _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).layoutHeader
      (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter 1) :
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.DenseMetadata ν (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter cap score := by
  obtain ⟨h1,h2,h3⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.metadata_reads_of_keptBut K
  exact ⟨h1.trans H.1,h2.trans H.2.1,h3.trans H.2.2⟩

theorem initial_dense_metadata
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC) :
    _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.DenseMetadata μ (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter
      (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))
      (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC) := H.dense.2

end ThreeSum.EncodedColorWantedConsumerData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Finite word bounds for every physical wanted mass

Each original triple has at most the established representation cap many
raw witnesses. The incidence coordinate is its physical position, so the
finite product bound retains every owner and every repeated value. The
injective physical wanted labels then bound every scan prefix by the same
global raw cardinality.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Finset
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout
open _root_.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout
open _root_.ThreeSum.BandRawA
open _root_.ThreeSum1960614.Machine.ThreeSum.BandRawA
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.ReportingHostWantedOriginal
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal

set_option maxHeartbeats 1900000
set_option maxRecDepth 15000

theorem wanted_finite_raw_card_le {h J N NB NC : ℕ} {P shift : ℤ}
    (T : Finset (_root_.ThreeSum.RawIncidences.Original (Fin N) (Fin NB) (Fin NC)))
    (a : Fin N→ℤ) (b : Fin NB→ℤ) (c : Fin NC→ℤ)
    (hP : 0<P) (hguard : 4*P≤_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P shift T a b c).card≤_root_.ThreeSum.ReportingHostWantedLayout.massBound N NB NC (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representationCap h J) := by
  have hc : T.card≤N*NB*NC := by
    simpa only [Fintype.card_prod,Fintype.card_fin,Nat.mul_assoc] using Finset.card_le_univ T
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedLayout.raw_card_le T a b c hP hguard).trans (Nat.mul_le_mul_right _ hc)

theorem wanted_finite_raw_card_le_magnitude {n N NB NC : ℕ} {P shift : ℤ}
    (T : Finset (_root_.ThreeSum.RawIncidences.Original (Fin N) (Fin NB) (Fin NC)))
    (a : Fin N→ℤ) (b : Fin NB→ℤ) (c : Fin NC→ℤ)
    (hP : 0<P) (hguard : 4*P≤_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))
    (hN : N≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) P shift T a b c).card≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^7 :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_finite_raw_card_le T a b c hP hguard).trans (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_mass_bound_le hN hB hC)

theorem wanted_global_card_le {n nA NB NC g P : ℕ} (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ)
    (hP : 0<P) (hguard : 4*(P : ℤ)≤_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))
    (hN : (_root_.ThreeSum.BandRawA.items nA g rs).length≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.globalItems (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) nA NB NC g P rs fA fB fC shift).card≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^7 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_finite_raw_card_le_magnitude (_root_.ThreeSum.BandRawA.finiteAllProducts nA NB NC g rs)
    (fun i => _root_.ThreeSum.BandRawA.valueAt nA g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)
    (by exact_mod_cast hP) hguard hN hB hC

theorem wanted_local_card_le {n nA NB NC g P : ℕ} (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (_root_.ThreeSum.ReportingHostWantedOriginal.AType nA g rs))
    (hP : 0<P) (hguard : 4*(P : ℤ)≤_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))
    (hN : (_root_.ThreeSum.BandRawA.items nA g rs).length≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.localItems (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) nA NB NC g P rs fA fB fC shift w).card≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^7 :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_finite_raw_card_le_magnitude (_root_.ThreeSum.BandRawA.finiteOwnerProduct nA NB NC g rs (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.owner rs w))
    (fun i => _root_.ThreeSum.BandRawA.valueAt nA g rs fA i.val) (fun j => fB j.val) (fun j => fC j.val)
    (by exact_mod_cast hP) hguard hN hB hC



theorem wanted_local_root_le {n nA NB NC g P : ℕ} (rs : List _root_.ThreeSum.BandCandidateRows.Record)
    (fA fB fC : ℕ→ℤ) (shift : ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (_root_.ThreeSum.ReportingHostWantedOriginal.AType nA g rs))
    (hP : 0<P) (hguard : 4*(P : ℤ)≤_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))
    (hN : (_root_.ThreeSum.BandRawA.items nA g rs).length≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedOriginal.localItems (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) nA NB NC g P rs fA fB fC shift w) w≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^7 := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostFrontierLayout.rootMass_eq]
  exact (Finset.card_filter_le _ _).trans (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_local_card_le rs fA fB fC shift w hP hguard hN hB hC)

section Physical

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ} {n nA NB NC g free P : ℕ}
  {rs : List _root_.ThreeSum.BandCandidateRows.Record} {shift : ℤ}
  (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output μ free (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)^_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
    (_root_.ThreeSum.LightGuardedWanted.left P (_root_.ThreeSum.BandRawA.values fA (_root_.ThreeSum.BandRawA.items nA g rs)))
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.right (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) (3*(_root_.ThreeSum.BandRawA.values fA (_root_.ThreeSum.BandRawA.items nA g rs)).length)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) shift)

theorem wanted_physical_slot_mass_le (i : ℕ)
    (hP : 0<P) (hguard : 4*(P : ℤ)≤_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))
    (hN : (_root_.ThreeSum.BandRawA.items nA g rs).length≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.slotMass H fB fC NB NC i≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^7 := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.slotMass
  split
  · exact _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_local_root_le rs fA fB fC shift _ hP hguard hN hB hC
  · exact Nat.zero_le _

theorem wanted_physical_prefix_mass_le (k : ℕ) (hk : k≤(μ free).toNat)
    (hP : 0<P) (hguard : 4*(P : ℤ)≤_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))
    (hN : (_root_.ThreeSum.BandRawA.items nA g rs).length≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    _root_.ThreeSum.SharedTraversalCosts.prefixMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.slotMass H fB fC NB NC) k≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^7 :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPrefix.prefix_mass_le_card H fB fC NB NC k hk).trans
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_global_card_le rs fA fB fC shift hP hguard hN hB hC)

end Physical
end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Polynomial call depth for scanning every physical wanted record

The scan retains the exact word and cell reservations of one wanted
dispatcher. Only its depth includes the number of physical records.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds

set_option maxHeartbeats 1700000
set_option maxRecDepth 14000





theorem wanted_scan_count_le {n N count : ℕ}
    (hN : N≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3)
    (hcount : count≤(3*N)*_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) :
    count≤_root_.ThreeSum.SharedReportingBankResourceBounds.wantedScanCount n := by
  have ho : _root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^2 :=
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.output_count_le_magnitude n
  calc
    _ ≤ (3*N)*_root_.ThreeSum1960614.Machine.ThreeSum.LightGuardedWanted.totalKeys (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) := hcount
    _ ≤ (9*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^3)*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^2 := Nat.mul_le_mul (by omega) ho
    _ = _root_.ThreeSum.SharedReportingBankResourceBounds.wantedScanCount n := by unfold _root_.ThreeSum.SharedReportingBankResourceBounds.wantedScanCount; ring

theorem wanted_scan_count_envelope (n : ℕ) : _root_.ThreeSum.SharedReportingBankResourceBounds.wantedScanCount n+4≤_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n := by
  have h5 := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_power_le n 5 10 (by decide)
  have h1 : 1≤(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^10 := Nat.one_le_pow _ _ (by omega)
  unfold _root_.ThreeSum.SharedReportingBankResourceBounds.wantedScanCount _root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope
  omega

theorem wanted_scan_step_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {n U dst d count : ℕ}
    (hcount : count≤_root_.ThreeSum.SharedReportingBankResourceBounds.wantedScanCount n) (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedScanNeed n U).Ok lim dst d) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst (d+count+4) :=
  hok.mono le_rfl le_rfl (by dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedScanNeed]; omega)

theorem wanted_scan_at_depth_of_ok {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {n U dst d count e : ℕ}
    (hcount : count≤_root_.ThreeSum.SharedReportingBankResourceBounds.wantedScanCount n) (he : e≤d+count+4)
    (hok : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedScanNeed n U).Ok lim dst d) : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst e :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_scan_step_of_ok hcount hok).mono le_rfl le_rfl (by omega)



noncomputable section



end
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





theorem label_position (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.label H s).1.val=_root_.ThreeSum.ReportingHostWantedConsumerData.rawIndex μ (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC) s.val %
      (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).N := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt_position H.wanted (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.slot H s)
  calc
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.label H s).1.val = _ := hh
    _ = _ := by
      simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.slot,_root_.ThreeSum.ReportingHostWantedConsumerData.rawIndex,_root_.ThreeSum.DenseGuardWanted.leftIndex,_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences,_root_.ThreeSum.BandRawA.values_length]

theorem label_output (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.label H s).2.2=_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeOriginal.output (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
      (_root_.ThreeSum.ReportingHostWantedConsumerData.outputIndex μ (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC) s.val) := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedPhysical.wantedAt_output H.wanted (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.slot H s)
  calc
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.label H s).2.2 = _ := hh
    _ = _ := by
      simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.slot,_root_.ThreeSum.ReportingHostWantedConsumerData.outputIndex,_root_.ThreeSum.DenseGuardWanted.rightIndex,_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config,_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorNormalizedData.incidences,_root_.ThreeSum.BandRawA.values_length,_root_.ThreeSum.SharedReportingBankResourceBounds.half,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks]

theorem slot_indices (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)) :
    _root_.ThreeSum.ReportingHostWantedConsumerData.rawIndex μ (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC) s.val<3*(_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).N ∧
      _root_.ThreeSum.ReportingHostWantedConsumerData.outputIndex μ (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC) s.val<_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)^_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n := by
  exact _root_.ThreeSum1960614.Machine.ThreeSum.DenseGuardWanted.output_bounds H.wanted (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.slot H s).isLt

theorem slot_reads (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)) :
    let cfg := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC
    μ (cfg.pairs+2*s.val)=(_root_.ThreeSum.ReportingHostWantedConsumerData.rawIndex μ cfg s.val : ℤ) ∧
      μ (cfg.pairs+2*s.val+1)=(_root_.ThreeSum.ReportingHostWantedConsumerData.outputIndex μ cfg s.val : ℤ) := by
  obtain ⟨i,j,_,_,hi,hj,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.WantedRecordCoverage.output_pair H.wanted (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.slot H s).isLt
  change μ ((_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).pairs+2*s.val)=(i : ℤ) at hi
  change μ ((_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).pairs+2*s.val+1)=(j : ℤ) at hj
  simp [_root_.ThreeSum.ReportingHostWantedConsumerData.rawIndex,_root_.ThreeSum.ReportingHostWantedConsumerData.outputIndex,hi,hj]

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

theorem hit_at (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.hit H s.val ↔ _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.labelHit n A B C hsA hsB hsC (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.label H s) := by
  exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedDecision.slotHit_at H.wanted
    (fun j => B.getD j 0) (fun j => C.getD j 0) B.length C.length
    (_root_.ThreeSum.LightSwitchDepth.depth (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.slot H s)

theorem stepTime_at (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.stepTime H s.val=
      _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatch.time (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC) (_root_.ThreeSum.SharedReportingBankResourceBounds.wantedDecodeV n)
        (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.recordTime free n A B C hsA hsB hsC (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.label H s)
          (_root_.ThreeSum.ReportingHostWantedConsumerData.outputIndex μ (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC) s.val)
          (_root_.ThreeSum.SharedTraversalCosts.prefixMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass H) s.val) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.threshold n A B C hsA hsB hsC)) := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.stepTime,dif_pos s.isLt]

theorem mass_le (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (i : ℕ) (hp : 0<_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (hg : 4*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)≤_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass H i≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^7 := by
  have hN := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.incidence_length_le_magnitude H
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.incidence_length_eq] at hN
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_physical_slot_mass_le H.wanted i hp hg hN
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.normalized_lengths H).2.1 (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.normalized_lengths H).2.2

theorem prefix_mass_le (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    {k : ℕ} (hk : k≤_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC)
    (hp : 0<_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (hg : 4*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)≤_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) :
    _root_.ThreeSum.SharedTraversalCosts.prefixMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass H) k≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^7 := by
  have hN := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.incidence_length_le_magnitude H
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.incidence_length_eq] at hN
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_physical_prefix_mass_le H.wanted k
    (by rw [_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count_read H,Int.toNat_natCast]; exact hk) hp hg hN
    (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.normalized_lengths H).2.1 (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumColorBudgets.normalized_lengths H).2.2

theorem slot_reads_of_keptBut (H : _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC))
    (K : _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).layoutHeader
      (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter 1) :
    let cfg := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC
    ν (cfg.pairs+2*s.val)=(_root_.ThreeSum.ReportingHostWantedConsumerData.rawIndex μ cfg s.val : ℤ) ∧
      ν (cfg.pairs+2*s.val+1)=(_root_.ThreeSum.ReportingHostWantedConsumerData.outputIndex μ cfg s.val : ℤ) := by
  let cfg := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC
  have he : cfg.pairs+2*_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC≤cfg.counter := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.persistent_ends H).pairs
  have hk := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.kept_counter K
  have hs := s.isLt
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.slot_reads H s
  exact ⟨(hk _ (by dsimp only [cfg] at *; omega)).trans hr.1,
    (hk _ (by dsimp only [cfg] at *; omega)).trans hr.2⟩

end ThreeSum.ReportingHostWantedConsumerData

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScanStored

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
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScanStored.program_meets__implementation_acecaa01e0 {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ→ℤ} {free n U d : ℕ}
    {color : _root_.ThreeSum.Coloring.Parameter (_root_.ThreeSum.Scales.inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (hx : ∀ i, |x i|≤(U : ℤ))
    (hp : 0<_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (hg : 4*(_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)≤_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n))
    (hthreshold : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.threshold n A B C hsA hsB hsC≤9*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^8)
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
          (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).counter 1) := by
  let cfg := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC
  let N := _root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC
  let Inv := fun ν => _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν cfg.layoutHeader cfg.counter 1
  have hcount : N≤_root_.ThreeSum.SharedReportingBankResourceBounds.wantedScanCount n :=
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_scan_count_le (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.incidence_length_le_magnitude H.encoded) (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.count_le_product H.encoded)
  have hspace : N+1≤lim.space := by
    have henv := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_scan_count_envelope n
    have hh := hok.cells
    change cfg.layoutHeader+_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n≤lim.space at hh
    omega
  have hD : d+N+1≤lim.depth := by
    have hh := hok.depth
    change d+(_root_.ThreeSum.SharedReportingBankResourceBounds.wantedEnvelope n+_root_.ThreeSum.SharedReportingBankResourceBounds.wantedScanCount n+4)≤lim.depth at hh
    omega
  have hstep : ∀ i<N, ∀ ν, ∀ e, e+i≤d+N+1 → Inv ν →
      ν cfg.counter=(_root_.ThreeSum.SharedTraversalCosts.prefixMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass H.encoded) i : ℤ) →
      _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatch.program 151 e (_root_.ThreeSum.LightReportingWantedDispatch.arguments cfg i)
        ν (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.stepTime H.encoded i)
        (fun r ξ => (r=0 ∨ r=1) ∧
          (r=1 ↔ _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.threshold n A B C hsA hsB hsC<_root_.ThreeSum.SharedTraversalCosts.prefixMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass H.encoded) i+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass H.encoded i ∨ _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.hit H.encoded i) ∧
          ξ cfg.counter=((_root_.ThreeSum.SharedTraversalCosts.prefixMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass H.encoded) i+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass H.encoded i : ℕ) : ℤ) ∧
          Inv ξ ∧ _root_.ThreeSum1960614.Machine.Light.KeptBut ν ξ cfg.layoutHeader cfg.counter 1) := by
    intro i hi ν e he hInv hcounter
    let s : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.ThreeSumWantedHostData.count n A B C hsA hsB hsC) := ⟨i,hi⟩
    obtain ⟨Hν,HQν⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.retained_of_keptBut H.encoded H.catalog hInv
    have hmeta := (_root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorWantedConsumerData.initial_dense_metadata H).of_keptBut hInv
    have hindices := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.slot_indices H.encoded s
    have hreads := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.slot_reads_of_keptBut H.encoded s hInv
    have hneed : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim cfg.layoutHeader (e+1) :=
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.wanted_scan_at_depth_of_ok hcount (by omega) hok
    have hmass : _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.labelMass n A B C hsA hsB hsC (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.label H.encoded s)≤3*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n)^7 := by
      rw [← _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass_at H.encoded s]
      exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass_le H.encoded i hp hg
    have hrun := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedDispatchStored.program_meets (d := e) Hν HQν hx (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.label H.encoded s)
      hi hindices.1 hindices.2 (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.label_position H.encoded s) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.label_output H.encoded s)
      hreads.1 hreads.2 hp hg (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.label_key H.encoded s) hcounter hmeta.1 hmeta.2.1
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.prefix_mass_le H.encoded hi.le hp hg) hmass hthreshold hneed
    let QR := fun (r : ℤ) ξ => (r=0 ∨ r=1) ∧
      (r=1 ↔ _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.threshold n A B C hsA hsB hsC<_root_.ThreeSum.SharedTraversalCosts.prefixMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass H.encoded) i+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass H.encoded i ∨ _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.hit H.encoded i) ∧
      ξ cfg.counter=((_root_.ThreeSum.SharedTraversalCosts.prefixMass (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass H.encoded) i+_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass H.encoded i : ℕ) : ℤ) ∧
      Inv ξ ∧ _root_.ThreeSum1960614.Machine.Light.KeptBut ν ξ cfg.layoutHeader cfg.counter 1
    have hrun' := hrun.mono (R' := QR) le_rfl (fun r ξ hr => by
      refine ⟨hr.1,?_,?_,?_,hr.2.2.2⟩
      · simpa only [← _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass_at H.encoded s,← _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.hit_at H.encoded s,s,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.threshold,_root_.ThreeSum.SharedReportingBankResourceBounds.half,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks] using hr.2.1
      · simpa only [← _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass_at H.encoded s] using hr.2.2.1
      · exact hInv.trans hr.2.2.2)
    have ht := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.stepTime_at H.encoded s
    change _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.stepTime H.encoded i = _ at ht
    rw [ht]
    exact hrun'
  have hscan := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScan.program_meets (C := cfg) (mass := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.mass H.encoded)
    (hit := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.hit H.encoded) (stepTime := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.stepTime H.encoded) (Inv := Inv)
    (threshold := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostWantedConsumerData.threshold n A B C hsA hsB hsC) (n := N) (N := N) (D := d+N) (d := d)
    hok.space hspace hD le_rfl le_rfl _root_.ThreeSum1960614.Machine.Light.SameOn.refl H.dense.1 hstep
  exact hscan.mono le_rfl (fun r ν hr => ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.2⟩)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScanStored.program_meets__implementation_acecaa01e0) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingWantedScanStored.program_meets__implementation_acecaa01e0)

#print axioms solution
