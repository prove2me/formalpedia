-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.source_span_le_magnitude
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:33:57.810885+00:00
-- url     : https://prove2.me/submissions/8491724e-9359-4850-a04f-9da188f5b622

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingBankResourceBounds_components
import Theorems.Thm_ThreeSum_SubsetAddress_enumerateLayer_nodup

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockSourceCatalogCosts
end ThreeSum.BlockSourceCatalogCosts
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
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
namespace ThreeSum.SourceBandBankLayout
end ThreeSum.SourceBandBankLayout
namespace ThreeSum.SourceBandBanksCosts
end ThreeSum.SourceBandBanksCosts
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts
end ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum1960614.Machine.ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
end ThreeSum1960614.Machine.ThreeSum.BlockSourceSharing
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
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
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
end ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts
end ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales

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



theorem work_address (base count W cut : ℕ) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.work base count W cut =
      base+count*(_root_.ThreeSum.LightBlockSourceBatchLayout.stride W cut+2)+_root_.ThreeSum.SubsetAddress.downsetCap W cut+W+2 := by
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.work _root_.ThreeSum.LightBlockSourceBatchLayout.rowOut _root_.ThreeSum.LightBlockSourceBatchLayout.bitBase _root_.ThreeSum.LightBlockSourceBatchLayout.maskBase _root_.ThreeSum.LightBlockSourceBatchLayout.slot _root_.ThreeSum.LightBlockSourceBatchLayout.banks
  ring





















end ThreeSum.BlockSourceCatalogCosts

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







theorem host_space_add (base free h J : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space (base+free) h J=
      base+_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space free h J := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space _root_.ThreeSum.LightSourcePreparation.space
    _root_.ThreeSum.LightBlockSourceHashes.space _root_.ThreeSum.LightSourceMaskFlags.space _root_.ThreeSum.LightSourceRetainedStages.space
  omega

















end ThreeSum.SourceBandBankLayout

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

















theorem overhead_bound (h J : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space 0 h J ≤
    J+2*(J*(464*h))+(J*(464*h)+1)^2+
      Nat.log 2 ((464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+1)+
      Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J+1)+20 := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space _root_.ThreeSum.LightSourcePreparation.space _root_.ThreeSum.LightBlockSourceHashes.space
    _root_.ThreeSum.LightSourceMaskFlags.space _root_.ThreeSum.LightSourceRetainedStages.space _root_.ThreeSum.LightPascal.tableSize
  omega

theorem span_eq (h J cut : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span h J cut=
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J*(_root_.ThreeSum.LightBlockSourceBatchLayout.stride (J*(464*h)) cut+2)+
      _root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut+J*(464*h)+2+_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space 0 h J := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.host_space_add
    (_root_.ThreeSum.LightBlockSourceBatchLayout.work 0 (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count h J) (J*(464*h)) cut) 0 h J
  simp only [Nat.add_zero] at h
  rw [h,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCatalogCosts.work_address]
  omega











end ThreeSum.SourceBandBanksCosts

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

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.SharedReportingBankResourceBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds

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
section

theorem ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.source_span_le_magnitude__implementation_f316c4b5e6 (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBankLayout.span (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) (2*_root_.ThreeSum.SharedReportingBankResourceBounds.half n*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) ≤ 100*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^3 := by
  have H := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.components n
  have hW := H.widthBound
  have hL := H.localWidthBound
  have hJ := H.blocksBound
  have hS := H.occurrence
  have hP := H.prime
  have hPP := H.primePower
  have hM := H.positive
  have hpower : 2^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans H.widthPower
  have hcap := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.downset_le_pow (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) (2*_root_.ThreeSum.SharedReportingBankResourceBounds.half n*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)).trans hpower
  have hlogP : Nat.log 2 ((464*_root_.ThreeSum.SharedReportingBankResourceBounds.half n)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)+1) ≤ (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^2 := by
    have hm := Nat.mul_le_mul (show 464*_root_.ThreeSum.SharedReportingBankResourceBounds.half n ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n by omega) hP
    exact (Nat.log_le_self _ _).trans (by nlinarith)
  have hlogE : Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)+1) ≤ (_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^2 := by
    have hm := Nat.mul_le_mul (show _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) ≤ _root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n by omega) hPP
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound
    change Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)*
      (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)^(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.SharedReportingBankResourceBounds.half n))+1) ≤ _
    exact (Nat.log_le_self _ _).trans (by nlinarith)
  have hscratch := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts.overhead_bound (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)
  change _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space 0 (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) ≤
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n+2*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)+(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)+1)^2+
    Nat.log 2 ((464*_root_.ThreeSum.SharedReportingBankResourceBounds.half n)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.SharedReportingBankResourceBounds.half n)+1)+
    Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)+1)+20 at hscratch
  have hquad := Nat.pow_le_pow_left hW 2
  have hwork : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space 0 (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) ≤ 30*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^2 := by
    nlinarith
  have hstride : _root_.ThreeSum.LightBlockSourceBatchLayout.stride (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) (2*_root_.ThreeSum.SharedReportingBankResourceBounds.half n*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)+2 ≤
      12*(_root_.ThreeSum.SharedReportingBankResourceBounds.magnitude n+1)^2 := by
    have hfamily := Nat.mul_le_mul hW hcap
    unfold _root_.ThreeSum.LightBlockSourceBatchLayout.stride _root_.ThreeSum.LightBlockSourceBatchLayout.family
    nlinarith
  have hprod := Nat.mul_le_mul hS hstride
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandBanksCosts.span_eq]
  change _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceCatalog.count (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)*
    (_root_.ThreeSum.LightBlockSourceBatchLayout.stride (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) (2*_root_.ThreeSum.SharedReportingBankResourceBounds.half n*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)+2)+
    _root_.ThreeSum.SubsetAddress.downsetCap (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)) (2*_root_.ThreeSum.SharedReportingBankResourceBounds.half n*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n)+2+
    _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space 0 (_root_.ThreeSum.SharedReportingBankResourceBounds.half n) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.blocks n) ≤ _
  nlinarith
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.source_span_le_magnitude__implementation_f316c4b5e6) := (@ThreeSum1960614.Machine.ThreeSum.SharedReportingBankResourceBounds.source_span_le_magnitude__implementation_f316c4b5e6)

#print axioms solution
