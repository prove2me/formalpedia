-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.resources
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:33:53.138274+00:00
-- url     : https://prove2.me/submissions/58df83e3-339b-4f71-a571-e5cfcd90ed71

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_offset_le
import Theorems.Thm_ThreeSum_LightRadixKeys_space_bound

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightRadixKeys
end ThreeSum.LightRadixKeys
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum.ReportingHostCatalogIndexCosts
end ThreeSum.ReportingHostCatalogIndexCosts
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
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightRadixKeys
end ThreeSum1960614.Machine.ThreeSum.LightRadixKeys
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
end ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogIndexCosts
end ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogIndexCosts
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
end ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
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
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

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

/-!
# Complete positional-key product construction

The three fixed procedures build every product stage. Each stage has a
computed length header followed by its literal key array. The recursive
caller reads the previous header and appends Cartesian rows. Its final
array contains every record sequence, retaining repeated keys.
-/

namespace ThreeSum.LightRadixKeys
open _root_.ThreeSum.LightRadixKeys


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.RadixKeyLists
open _root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000












theorem word_mono {p U j k : ℕ} (hj : j ≤ k) : _root_.ThreeSum.LightRadixKeys.word p U j ≤ _root_.ThreeSum.LightRadixKeys.word p U k := by
  have hpow := Nat.pow_le_pow_right (by omega : 1 ≤ p+1) hj
  have hv := Nat.mul_le_mul_left U hpow
  have hpv := Nat.mul_le_mul_left p hv
  unfold _root_.ThreeSum.LightRadixKeys.word _root_.ThreeSum.LightRadixRows.word
  omega







variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}







end ThreeSum.LightRadixKeys

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual complete shared prefix catalog from the original source tables

A single closed program constructs every aligned prefix-mask pair, reads its
computed count header, and builds all local suffix box tables. The original
record order is exact; no supplied enumeration, count, or table pointer is
used as an algorithmic oracle.
-/

namespace ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingPrefixCatalog


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}











theorem count_pos (h k : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k := by
  exact Nat.pow_pos (Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))







end ThreeSum.LightReportingPrefixCatalog

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

/-!
# The actual sorted index stays within polynomial mask-width overhead

Complete prefix catalogs have at most 2^(2W) records. This bounds both the
merge-sort logarithm and the binary-remainder scratch/time by the mask width,
so lookup contributes no linear factor in the catalog size to a query.
-/

namespace ThreeSum.ReportingHostCatalogIndexCosts
open _root_.ThreeSum.ReportingHostCatalogIndexCosts


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal

set_option maxHeartbeats 300000







theorem sort_clog_le {W n : ℕ} (hn : n ≤ 2^(2*W)) : Nat.clog 2 n ≤ 2*W :=
  Nat.clog_le_of_le_pow hn









end ThreeSum.ReportingHostCatalogIndexCosts

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












theorem levels_le (J : ℕ) : _root_.ThreeSum.SharedReportingBankHeader.levels J ≤ J+1 := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.level_le (show _root_.ThreeSum.LightSwitchDepth.depth J ≤ _root_.ThreeSum.LightSwitchDepth.depth J from le_rfl)
  unfold _root_.ThreeSum.SharedReportingBankHeader.levels
  omega

theorem count_le {h J k : ℕ} (hk : k ≤ _root_.ThreeSum.SharedReportingBankHeader.levels J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.prefixCount h J :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.prefix_count_le_pow (hk.trans (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.levels_le J))

theorem storage_le {h J k : ℕ} (hk : k ≤ _root_.ThreeSum.SharedReportingBankHeader.levels J) : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.prefixSpan h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.prefixStorage h J := by
  have hE : 1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h := by
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count_pos h 1
    exact Nat.succ_le_of_lt (by
      simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count,pow_one,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth] using hh)
  have hspace := _root_.ThreeSum.LightRadixKeys.space_bound 0 (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h) k hE
  have hcount := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.count_le (h := h) hk
  change (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h)^k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.prefixCount h J at hcount
  have hspace' : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.prefixSpan h k ≤ (k+1)*((_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h)^k+1) := by
    simpa only [_root_.ThreeSum.LightRadixKeys.space,Nat.zero_add,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.prefixSpan,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth] using hspace
  exact hspace'.trans (Nat.mul_le_mul (Nat.add_le_add_right hk 1) (Nat.add_le_add_right hcount 1))

theorem local_pairs_le (h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h ≤ 2^(2*(464*h)) := by
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count,pow_one,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth,Nat.one_mul] using
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.prefix_count_le_pow (h := h) (J := 1) (k := 1) le_rfl)





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

theorem index_word_mono {W a b : ℕ} (hab : a ≤ b) :
    _root_.ThreeSum.LightReportingSortedCatalog.word W a ≤ _root_.ThreeSum.LightReportingSortedCatalog.word W b := by
  have hm := Nat.mul_le_mul_left ((2^W)^2) (Nat.add_le_add_right hab 1)
  unfold _root_.ThreeSum.LightReportingSortedCatalog.word _root_.ThreeSum.LightReportingPackKeys.word
  omega



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
open _root_.ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels
open _root_.ThreeSum.SharedReportingBankHeader
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader
open _root_.ThreeSum.SharedReportingBankRows
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows
set_option maxHeartbeats 2800000
set_option maxRecDepth 14000
section

theorem ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.resources__implementation_44ff5d34fc {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {free h J NB NC g n d : ℕ}
    (hB : NB ≤ n) (hC : NC ≤ n)
    (hspace : free+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.extent h J n ≤ lim.space)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.word h J n g : ℤ) ≤ lim.word)
    (hdepth : d+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.depth h J ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingHost.Resources lim free h J NB NC g d := by
  have budget (x : ℕ) (hx : x ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.word h J n g) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hs := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.space_le (free := free) (h := h) (J := J) (g := g) hB hC).trans hspace
  have hend : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankHeader.finish free h J NB NC g ≤ lim.space := (le_max_right _ _).trans hs
  have hNB := (_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le NB g).trans hB
  have hNC := (_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le NC g).trans hC
  have hmul := Nat.mul_le_mul_left (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) hNB
  have hcount := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.count_le (h := h) (J := J) (k := _root_.ThreeSum.SharedReportingBankHeader.levels J) le_rfl
  have hstorage := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.storage_le (h := h) (J := J) (k := _root_.ThreeSum.SharedReportingBankHeader.levels J) le_rfl
  have hpowNonneg : (0 : ℤ) ≤ ((2^(464*h) : ℕ) : ℤ) := Int.natCast_nonneg _
  have hpairPowNonneg : (0 : ℤ) ≤ ((2^(2*(464*h)) : ℕ) : ℤ) := Int.natCast_nonneg _
  refine ⟨hs,budget _ ?_,budget _ ?_,budget _ ?_,budget _ ?_,budget _ ?_,?_,?_⟩
  · unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingBank.controlWord _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.word _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.control
    omega
  · unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.word; omega
  · unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.word; omega
  · have he := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.local_pairs_le h
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.word
    omega
  · unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.word; omega
  · unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.depth at hdepth
    omega
  · intro q hq
    refine ⟨budget _ ?_,?_,budget _ ?_,?_,budget _ ?_,?_,?_,?_,?_,?_,?_⟩
    · unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.word _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.stateWord
      omega
    · rw [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rowBase_next]
      exact (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.rowBase_mono _ h J (_root_.ThreeSum.SharedReportingBankHeader.levels J) (show q+1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankRows.total h J NB NC g from hq)).trans hend
    · unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.word; omega
    · intro k hk
      have hkJ : k ≤ J := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.level_le (show k ≤ _root_.ThreeSum.LightSwitchDepth.depth J by unfold _root_.ThreeSum.SharedReportingBankHeader.levels at hk; omega)
      apply budget
      have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightRadixKeys.word_mono (p := 2^(464*h)) (U := 2^(464*h)) hkJ
      unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.word
      omega
    · unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.word _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth
      omega
    · intro k hk
      have hkJ : k ≤ J := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.level_le (show k ≤ _root_.ThreeSum.LightSwitchDepth.depth J by unfold _root_.ThreeSum.SharedReportingBankHeader.levels at hk; omega)
      have hc := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.index_word_mono (W := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.prefix_count_le_pow (h := h) hkJ)
      apply budget
      change _root_.ThreeSum.LightReportingSortedCatalog.word (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k) ≤ _
      change _root_.ThreeSum.LightReportingSortedCatalog.word (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k) ≤
        _root_.ThreeSum.LightReportingSortedCatalog.word (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J) (2^(2*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J)) at hc
      unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.word
      omega
    · intro k hk
      have hv : (J-k)*(464*h) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hv
      have hm := Nat.mul_le_mul hp (Nat.mul_le_mul (Nat.mul_le_mul_right g hp) (Nat.mul_le_mul_right g hp))
      apply budget
      unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.word
      omega
    · intro k hk
      have hr : _root_.ThreeSum.SharedReportingBankLevels.residual h J k ≤ 2*h*J := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      have ht := Nat.pow_le_pow_left (show J+_root_.ThreeSum.SharedReportingBankLevels.residual h J k+1000000001 ≤ J+2*h*J+1000000001 by omega) 96
      apply budget
      change (J+_root_.ThreeSum.SharedReportingBankLevels.residual h J k+1000000001)^96 ≤ _
      unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.word
      omega
    · unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.depth at hdepth
      omega
    · unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.depth _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth at hdepth
      omega
    · intro k hk
      have hkJ : k ≤ J := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLevels.level_le (show k ≤ _root_.ThreeSum.LightSwitchDepth.depth J by unfold _root_.ThreeSum.SharedReportingBankHeader.levels at hk; omega)
      have hc := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogIndexCosts.sort_clog_le (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.prefix_count_le_pow (h := h) hkJ)
      unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.depth _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth at hdepth
      omega
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.resources__implementation_44ff5d34fc) := (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.resources__implementation_44ff5d34fc)

#print axioms solution
