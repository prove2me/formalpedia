-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.query_scratch
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:30:04.34452+00:00
-- url     : https://prove2.me/submissions/da105716-f5f6-42ae-ab22-b54e7ae7b1ee

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankLevels_candidates_nonempty
import Theorems.Thm_ThreeSum_SubsetAddress_enumerateLayer_nodup

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightLocalCoverMagnitude
end ThreeSum.LightLocalCoverMagnitude
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingSuffixBoxes
end ThreeSum.LightReportingSuffixBoxes
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightSwitch
end ThreeSum.LightSwitch
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.ReportingHostPackedCatalog
end ThreeSum.ReportingHostPackedCatalog
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows
namespace ThreeSum.SharedReportingBankSources
end ThreeSum.SharedReportingBankSources
namespace ThreeSum.SourceBandFinite
end ThreeSum.SourceBandFinite
namespace ThreeSum.SourceBandLayout
end ThreeSum.SourceBandLayout
namespace ThreeSum.SourceBandPartition
end ThreeSum.SourceBandPartition
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614
end ThreeSum1960614
namespace ThreeSum1960614.LightQuarticSwitch
end ThreeSum1960614.LightQuarticSwitch
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBoxes
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBoxes
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightSwitch
end ThreeSum1960614.Machine.ThreeSum.LightSwitch
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
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
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandFinite
end ThreeSum1960614.Machine.ThreeSum.SourceBandFinite
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
end ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandPartition
end ThreeSum1960614.Machine.ThreeSum.SourceBandPartition
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum1960614
end ThreeSum1960614.Machine.ThreeSum1960614
namespace ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch
end ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch

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
The actual quartic integer test and its Light-language execution contract.
The finite scan and proof structure adapt the pinned Apache-2.0 source
Submission/ThreeSum/LightSwitch{,Bounds}.lean, commit
2b639655e07421b9ac743de9090459bab473a7c0.
The coefficients, powers and resource allowances below are changed to
the exact expansion-232 degree-four comparison in PROOF.md, Section 4.2.
-/

namespace ThreeSum1960614.LightQuarticSwitch
open _root_.ThreeSum1960614.LightQuarticSwitch


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000

















@[simp] theorem mem_candidates {J j r q : ℕ} :
    q ∈ _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.candidates J j r ↔ q ≤ r/2 ∧ _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.accepts J j r q := by
  simp [_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.candidates, Nat.lt_succ_iff]

theorem index_mem {J j r : ℕ} (h : (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.candidates J j r).Nonempty) :
    _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index J j r ∈ _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.candidates J j r := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index, dif_pos h]
  exact Finset.min'_mem _ _







theorem index_le_residual {J j r : ℕ} (hne : (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.candidates J j r).Nonempty) :
    _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index J j r ≤ r :=
  (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.mem_candidates.mp (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index_mem hne)).1.trans (Nat.div_le_self _ _)









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {μ : ℕ→ℤ} {J j r q d : ℕ}













end ThreeSum1960614.LightQuarticSwitch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Compact addresses for bounded-cardinality bit masks

Both ranking and enumeration recurse on the highest available bit. The
enumerator stops immediately when the requested layer is empty. In
particular, it does not enumerate the ambient Boolean cube and filter it.
-/

namespace ThreeSum.SubsetAddress
open _root_.ThreeSum.SubsetAddress


set_option maxRecDepth 4000

open _root_.Finset
open scoped _root_.BigOperators















































@[simp] theorem layerOffset_zero (L : ℕ) : _root_.ThreeSum.SubsetAddress.layerOffset L 0 = 0 := by
  simp [_root_.ThreeSum.SubsetAddress.layerOffset]

theorem layerOffset_succ (L k : ℕ) :
    _root_.ThreeSum.SubsetAddress.layerOffset L (k + 1) = _root_.ThreeSum.SubsetAddress.layerOffset L k + L.choose k := by
  exact Finset.sum_range_succ _ _

















theorem enumerateThrough_length (L k : ℕ) :
    (_root_.ThreeSum.SubsetAddress.enumerateThrough L k).length = _root_.ThreeSum.SubsetAddress.layerOffset L (k + 1) := by
  induction k with
  | zero => simp [_root_.ThreeSum.SubsetAddress.enumerateThrough, _root_.ThreeSum.SubsetAddress.enumerateLayer_length, _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ]
  | succ k ih =>
      rw [_root_.ThreeSum.SubsetAddress.enumerateThrough, List.length_append, ih, _root_.ThreeSum.SubsetAddress.enumerateLayer_length,
        _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ L (k + 1)]

theorem enumerateDownset_length (L cut : ℕ) :
    (_root_.ThreeSum.SubsetAddress.enumerateDownset L cut).length = _root_.ThreeSum.SubsetAddress.downsetCap L cut :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.enumerateThrough_length L (min cut L)

theorem mem_enumerateThrough (L k m : ℕ) :
    m ∈ _root_.ThreeSum.SubsetAddress.enumerateThrough L k ↔ m < 2 ^ L ∧ _root_.ThreeSum.SubsetAddress.weight L m ≤ k := by
  induction k with
  | zero => simp [_root_.ThreeSum.SubsetAddress.enumerateThrough, _root_.ThreeSum.SubsetAddress.mem_enumerateLayer, _root_.ThreeSum.SubsetAddress.IsMask]
  | succ k ih =>
      simp only [_root_.ThreeSum.SubsetAddress.enumerateThrough, List.mem_append, ih, _root_.ThreeSum.SubsetAddress.mem_enumerateLayer, _root_.ThreeSum.SubsetAddress.IsMask]
      omega

theorem mem_enumerateDownset (L cut m : ℕ) :
    m ∈ _root_.ThreeSum.SubsetAddress.enumerateDownset L cut ↔ m < 2 ^ L ∧ _root_.ThreeSum.SubsetAddress.weight L m ≤ cut := by
  rw [_root_.ThreeSum.SubsetAddress.enumerateDownset, _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.mem_enumerateThrough]
  constructor
  · rintro ⟨hm, hk⟩
    exact ⟨hm, hk.trans (min_le_left _ _)⟩
  · rintro ⟨hm, hk⟩
    exact ⟨hm, le_min hk (_root_.ThreeSum.SubsetAddress.weight_le_width hm)⟩

theorem enumerateThrough_nodup (L k : ℕ) : (_root_.ThreeSum.SubsetAddress.enumerateThrough L k).Nodup := by
  induction k with
  | zero => exact _root_.ThreeSum.SubsetAddress.enumerateLayer_nodup L 0
  | succ k ih =>
      apply ih.append (_root_.ThreeSum.SubsetAddress.enumerateLayer_nodup L (k + 1))
      intro m hm hn
      have ht := (_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.mem_enumerateThrough L k m).mp hm
      have hk := (_root_.ThreeSum.SubsetAddress.mem_enumerateLayer L (k + 1) m).mp hn
      have hw := hk.2
      omega

theorem enumerateDownset_nodup (L cut : ℕ) : (_root_.ThreeSum.SubsetAddress.enumerateDownset L cut).Nodup :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.enumerateThrough_nodup L (min cut L)













































end ThreeSum.SubsetAddress

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # One uniform exponential bound for all finite local-cover dimensions -/

namespace ThreeSum.LightLocalCoverMagnitude
open _root_.ThreeSum.LightLocalCoverMagnitude


open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout





theorem succ_pow_bound {x e : ℕ} (hx : x ≤ 2^e) : x+1 ≤ 2^(e+1) := by
  have hp := Nat.two_pow_pos e
  rw [pow_succ]
  omega







end ThreeSum.LightLocalCoverMagnitude

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual shrinking-suffix box preprocessing for an original valid block prefix -/

namespace ThreeSum.LightReportingSuffixBoxes
open _root_.ThreeSum.LightReportingSuffixBoxes


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]



theorem residual_le_suffix {h J k : ℕ} : _root_.ThreeSum.LightBlockQuery.residualSize h J k ≤ _root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k := by
  exact Nat.mul_le_mul_left (J-k) (by omega)



end ThreeSum.LightReportingSuffixBoxes

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! Compatibility interface consumed by the full reporting driver.
It delegates to the proved degree-four Light procedure. No cubic test or
separate callback implementation remains in this execution path. -/

namespace ThreeSum.LightSwitch
open _root_.ThreeSum.LightSwitch

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light










theorem index_le_residual {J j r : ℕ} (hne : (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.candidates J j r).Nonempty) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Switch.switchIndex J j r ≤ r :=
  _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index_le_residual hne









end ThreeSum.LightSwitch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact finite original-position sources for real and padded bands -/

namespace ThreeSum.SourceBandPartition
open _root_.ThreeSum.SourceBandPartition


open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.SourceBandLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout











theorem source_card (n g i : ℕ) : (_root_.ThreeSum.SourceBandPartition.source n g i).card=_root_.ThreeSum.SourceBandLayout.len n g i := by
  simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr (_root_.ThreeSum.SourceBandPartition.equiv n g i)).symm









end ThreeSum.SourceBandPartition

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact sorted lookup of a prefix catalog record

Each original catalog position is retained as the low digit of a packed
integer. A sorted search uses the upper end of the requested key's interval;
the unique prefix-key proof forces that hit to be the original record, and
remainder recovers its unchanged catalog index.
-/

namespace ThreeSum.ReportingHostPackedCatalog
open _root_.ThreeSum.ReportingHostPackedCatalog


open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder

set_option maxHeartbeats 600000































theorem prefix_count_le_pow {h J k : ℕ} (hk : k ≤ J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ 2^(2*(J*(464*h))) := by
  have hhalf : 2*h ≤ 464*h := by omega
  have he : _root_.ThreeSum.LightReportingPrefixArrays.localCount (464*h) h ≤ 2^(2*(464*h)) := by
    calc
      _ ≤ 2^(464*h)*2^(2*h) := Nat.mul_le_mul (Nat.choose_le_two_pow _ _) (Nat.choose_le_two_pow _ _)
      _ ≤ 2^(464*h)*2^(464*h) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hhalf)
      _ = 2^(2*(464*h)) := by rw [← pow_add]; congr 1; omega
  calc
    _ ≤ (2^(2*(464*h)))^k := Nat.pow_le_pow_left he k
    _ = 2^(2*(k*(464*h))) := by rw [← pow_mul]; congr 1; ring
    _ ≤ 2^(2*(J*(464*h))) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hk))

end ThreeSum.ReportingHostPackedCatalog

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







end ThreeSum.SourceBandFinite

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



theorem switch_le {h J k : ℕ} (hk : k ≤ _root_.ThreeSum.LightSwitchDepth.depth J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.switch h J k ≤ _root_.ThreeSum.SharedReportingBankLevels.residual h J k :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitch.index_le_residual (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.candidates_nonempty hk)

theorem boxCut_le (h J k : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k ≤ _root_.ThreeSum.SharedReportingBankLevels.residual h J k := Nat.sub_le _ _



























end ThreeSum.SharedReportingBankLevels

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retained source pointers and complete source families precede the bank end -/

namespace ThreeSum.SharedReportingBankSources
open _root_.ThreeSum.SharedReportingBankSources


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding



theorem source_card_le (n g i : ℕ) : (_root_.ThreeSum.SourceBandPartition.source n g i).card ≤ g := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPartition.source_card]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.length_le n g i





end ThreeSum.SharedReportingBankSources

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










theorem downset_le_pow (W cut : ℕ) : _root_.ThreeSum.SubsetAddress.downsetCap W cut ≤ 2^W := by
  have hn := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.enumerateDownset_nodup W cut
  have hsub : (_root_.ThreeSum.SubsetAddress.enumerateDownset W cut).toFinset ⊆ Finset.range (2^W) := by
    intro m hm
    exact Finset.mem_range.mpr ((_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.mem_enumerateDownset W cut m).mp (List.mem_toFinset.mp hm)).1
  have hc := Finset.card_le_card hsub
  simpa [List.toFinset_card_of_nodup hn,_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.enumerateDownset_length] using hc





















end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Concrete scratch limits for queries into the retained shared catalog bank

One mask span of `2^W` works for every prescribed level. The remaining
workspace is polynomial in W, including the exact packed-key remainder
workspace. Both source cardinalities are bounded independently by the
physical band size, and the switch and cut are the executed bank values.
-/

namespace ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum.SharedReportingBankResourceBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000





theorem query_items_le {c t : ℕ} (ht : t ≤ c) :
    _root_.ThreeSum.LightSparseQuery.queryItems c t ≤ 2^c := by
  simpa only [_root_.ThreeSum.LightSparseQuery.queryItems,_root_.ThreeSum.SubsetAddress.downsetCap,Nat.min_eq_left ht,_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ]
    using _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.downset_le_pow c t

theorem query_lookup_word_mono {W a b : ℕ} (hab : a ≤ b) :
    _root_.ThreeSum.LightReportingCatalogLookup.word W a ≤ _root_.ThreeSum.LightReportingCatalogLookup.word W b := by
  have hmul := Nat.mul_le_mul_left (2^(2*W)) (Nat.add_le_add_right hab 1)
  unfold _root_.ThreeSum.LightReportingCatalogLookup.word _root_.ThreeSum.LightReportingCatalogLookup.valueBound
  omega

theorem query_lookup_log_le {W N : ℕ} (hN : N ≤ 2^(2*W)) :
    Nat.log 2 (_root_.ThreeSum.LightReportingCatalogLookup.valueBound W N+1) ≤ 4*W+2 := by
  have hn := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude.succ_pow_bound hN
  have hv : _root_.ThreeSum.LightReportingCatalogLookup.valueBound W N ≤ 2^(4*W+1) := by
    calc
      _ ≤ 2^(2*W)*2^(2*W+1) := Nat.mul_le_mul_left _ hn
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hl := Nat.log_mono_right (b := 2) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMagnitude.succ_pow_bound hv)
  rw [Nat.log_pow (by decide)] at hl
  omega

theorem query_band_card_le (n g i : ℕ) : (_root_.ThreeSum.BandRawA.finiteBandPositions n g i).card ≤ g := by
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandFinite.source_eq_finiteBandPositions]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankSources.source_card_le n g i

theorem query_catalog_parameters {report h J NB NC g s i j k : ℕ}
    (hk : k ≤ _root_.ThreeSum.LightSwitchDepth.depth J) :
    let D := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.levelCatalog report h J NB NC g s i j k
    D.t ≤ _root_.ThreeSum.LightBlockQuery.residualSize h J k ∧
      D.boxCut ≤ _root_.ThreeSum.LightBlockQuery.residualSize h J k ∧
      _root_.ThreeSum.LightBlockQuery.residualSize h J k-D.t=D.boxCut := by
  change _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.switch h J k ≤ (J-k)*(2*h) ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k ≤ (J-k)*(2*h) ∧
    (J-k)*(2*h)-_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.switch h J k=_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut h J k
  rw [show (J-k)*(2*h)=_root_.ThreeSum.SharedReportingBankLevels.residual h J k by
    unfold _root_.ThreeSum.SharedReportingBankLevels.residual; ring]
  exact ⟨_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.switch_le hk,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.boxCut_le h J k,rfl⟩

theorem query_masks_le {report h J NB NC g s i j k : ℕ}
    (hk : k ≤ _root_.ThreeSum.LightSwitchDepth.depth J) :
    _root_.ThreeSum.LightSparseQuery.queryItems (_root_.ThreeSum.LightBlockQuery.residualSize h J k)
      (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.levelCatalog report h J NB NC g s i j k).t ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.queryMaskSpan h J := by
  have ht := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.query_catalog_parameters (report := report) (NB := NB) (NC := NC)
    (g := g) (s := s) (i := i) (j := j) (h := h) hk).1
  have hv : _root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.query_items_le ht).trans (Nat.pow_le_pow_right (by decide)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBoxes.residual_le_suffix.trans hv))



end ThreeSum.SharedReportingBankResourceBounds

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
section

theorem ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.query_scratch__implementation_e531016c96 {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {report h J NB NC g s i j k maskBase work : ℕ}
    (hk : k ≤ _root_.ThreeSum.LightSwitchDepth.depth J)
    (hmasks : maskBase+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.queryMaskSpan h J ≤ work)
    (hspace : work+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.queryWorkSpan h J ≤ lim.space)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.queryWord h J g : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Scratch lim h J k
      (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.levelCatalog report h J NB NC g s i j k)
      (_root_.ThreeSum.BandRawA.finiteBandPositions NB g i).card
      (_root_.ThreeSum.BandRawA.finiteBandPositions NC g j).card maskBase work := by
  let D := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankAccess.levelCatalog report h J NB NC g s i j k
  have hpar := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.query_catalog_parameters (report := report) (NB := NB) (NC := NC)
    (g := g) (s := s) (i := i) (j := j) (h := h) hk
  have hmask := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.query_masks_le (report := report) (NB := NB) (NC := NC)
    (g := g) (s := s) (i := i) (j := j) (h := h) hk
  have hN := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.prefix_count_le_pow (h := h)
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.level_le hk)
  have hlog := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.query_lookup_log_le hN
  have hlookup := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.query_lookup_word_mono (W := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J) hN
  have hv : _root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hv
  have hB := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.query_band_card_le NB g i
  have hC := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.query_band_card_le NC g j
  have hvalue : _root_.ThreeSum.LightSparseQuery.magnitudeBound
      (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k)
      (_root_.ThreeSum.LightBlockQuery.residualSize h J k) D.t
      (_root_.ThreeSum.BandRawA.finiteBandPositions NB g i).card (_root_.ThreeSum.BandRawA.finiteBandPositions NC g j).card ≤
      (2^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J)+1)*(2^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J)*((2^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J)*g)*(2^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J)*g))) :=
    Nat.mul_le_mul (Nat.add_le_add_right hmask 1)
      (Nat.mul_le_mul hp (Nat.mul_le_mul (Nat.mul_le_mul hp hB) (Nat.mul_le_mul hp hC)))
  have budget (x : ℕ) (hx : x ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.queryWord h J g) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  refine ⟨(Nat.add_le_add_left hmask maskBase).trans hmasks,?_,?_,?_,
    budget _ ?_,budget _ ?_,budget _ ?_,by omega,hpar.2.1,hpar.2.2.le⟩
  · unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.queryWorkSpan at hspace
    unfold _root_.ThreeSum.LightPascal.tableSize
    dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth,_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width] at *
    omega
  · unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.queryWorkSpan at hspace
    dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth,_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width] at *
    omega
  · unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.queryWorkSpan at hspace
    dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth,_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width] at *
    omega
  · unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.queryWord
    dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth,_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width] at *
    omega
  · unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.queryWord
    dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth,_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width] at *
    omega
  · unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.queryWord
    exact hvalue.trans (Nat.le_add_left _ _)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.query_scratch__implementation_e531016c96) := (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.query_scratch__implementation_e531016c96)

#print axioms solution
