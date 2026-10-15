-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.cell_le
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:17:50.399825+00:00
-- url     : https://prove2.me/submissions/0d130f72-149f-4ce0-818b-969c4ffc83ae

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
import Theorems.Thm_ThreeSum_LightRadixKeys_space_bound
import Theorems.Thm_ThreeSum_SubsetAddress_enumerateLayer_nodup

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
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
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
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

theorem ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.cell_le__implementation_3a0d7e60d5 {h J k cut : ℕ} (hk : k < _root_.ThreeSum.SharedReportingBankHeader.levels J) : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cellSize h J k cut ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.cellBound h J := by
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.count_le (h := h) hk.le
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.storage_le (h := h) hk.le
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.local_pairs_le h
  have hh : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localChoose h ≤ 2^(464*h) := Nat.choose_le_two_pow _ _
  have hv : (J-k)*(464*h) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hcap : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cap h J k cut ≤ 2^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J) :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.downset_le_pow _ _).trans (Nat.pow_le_pow_right (by decide) hv)
  have hbox := Nat.mul_le_mul hc
    (Nat.mul_le_mul (Nat.add_le_add_right hv 1) hcap)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cellSize _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL
    _root_.ThreeSum.LightReportingSuffixCatalog.stride _root_.ThreeSum.LightPascal.tableSize _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.cellBound
  change _ ≤ _ at hbox
  simp only [Nat.zero_add]
  dsimp only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.suffixWidth,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cap,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth] at *
  nlinarith
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.cell_le__implementation_3a0d7e60d5) := (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.cell_le__implementation_3a0d7e60d5)

#print axioms solution
