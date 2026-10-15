-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.initial_le_layer
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:52:35.901009+00:00
-- url     : https://prove2.me/submissions/b56f5923-c1b8-48b9-8d69-d237a0fb21fd

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
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
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
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
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
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
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
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
import Theorems.Thm_ThreeSum_LightReportingSuffixQuery_time_bound

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingCatalogQuery
end ThreeSum.LightReportingCatalogQuery
namespace ThreeSum.LightReportingSuffixBoxes
end ThreeSum.LightReportingSuffixBoxes
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightReportingSuffixLower
end ThreeSum.LightReportingSuffixLower
namespace ThreeSum.LightReportingSuffixQueryHost
end ThreeSum.LightReportingSuffixQueryHost
namespace ThreeSum.LightReportingSuffixQueryIndexed
end ThreeSum.LightReportingSuffixQueryIndexed
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostCatalogIndexCosts
end ThreeSum.ReportingHostCatalogIndexCosts
namespace ThreeSum.ReportingHostPackedCatalog
end ThreeSum.ReportingHostPackedCatalog
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.ReportingHostSuffixCosts
end ThreeSum.ReportingHostSuffixCosts
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
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
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery
end ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBoxes
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBoxes
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixLower
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixLower
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQueryHost
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQueryHost
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQueryIndexed
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQueryIndexed
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.MaskErase
end ThreeSum1960614.Machine.ThreeSum.MaskErase
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogIndexCosts
end ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogIndexCosts
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogSelection
end ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogSelection
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
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixCosts
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixCosts
namespace ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
end ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
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

















































theorem layerOffset_succ (L k : ℕ) :
    _root_.ThreeSum.SubsetAddress.layerOffset L (k + 1) = _root_.ThreeSum.SubsetAddress.layerOffset L k + L.choose k := by
  exact Finset.sum_range_succ _ _









































































end ThreeSum.SubsetAddress

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact bridge from row-major machine masks to the block reporting query

The explicit coordinate equivalence sends the remaining blocks to a
contiguous suffix. Transport of finite subset sums identifies the machine's
Möbius value with the concrete forced-prefix count used by reporting.
-/

namespace ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockIndexedQuery


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open scoped _root_.BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false





theorem suffixStage_le (J L k : ℕ) : _root_.ThreeSum.BlockIndexedQuery.suffixStage J L k ≤ J*L :=
  Nat.mul_le_mul_right L (Nat.sub_le _ _)



























section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]



















end Histograms

end ThreeSum.BlockIndexedQuery

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

/-!
# Actual global-to-local suffix-mask conversion

The program constructs powers once, tests each suffix coordinate using the
verified mask-bit procedure, and accumulates its local power. Runtime is
quadratic in the width, independent of the numeric mask value.
-/

namespace ThreeSum.LightReportingSuffixLower
open _root_.ThreeSum.LightReportingSuffixLower


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum.MaskErase
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}





















theorem time_bound {W V : ℕ} (hV : V ≤ W) : _root_.ThreeSum.LightReportingSuffixLower.time W V ≤ 400*(W+1)^2 := by
  have hm := Nat.mul_le_mul_right (_root_.ThreeSum.LightMaskErase.time W+100) hV
  unfold _root_.ThreeSum.LightReportingSuffixLower.time _root_.Light.powTableTime _root_.ThreeSum.LightMaskErase.time at *
  nlinarith

end ThreeSum.LightReportingSuffixLower

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # The actual local box construction is charged to the suffix binomial layer -/

namespace ThreeSum.ReportingHostSuffixCosts
open _root_.ThreeSum.ReportingHostSuffixCosts


open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open scoped _root_.BigOperators

theorem choose_le_cut {V j cut : ℕ} (hj : j ≤ cut) (hhalf : cut ≤ V/2) :
    V.choose j ≤ V.choose cut := by
  induction cut,hj using Nat.le_induction with
  | base => exact le_rfl
  | succ cut hj ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem downsetCap_le_layer {V cut : ℕ} (hhalf : cut ≤ V/2) :
    _root_.ThreeSum.SubsetAddress.downsetCap V cut ≤ (cut+1)*V.choose cut := by
  have hcut : cut ≤ V := hhalf.trans (Nat.div_le_self _ _)
  simp only [_root_.ThreeSum.SubsetAddress.downsetCap,Nat.min_eq_left hcut,_root_.ThreeSum.SubsetAddress.layerOffset]
  calc
    _ ≤ ∑ _j ∈ Finset.range (cut+1), V.choose cut := by
      apply Finset.sum_le_sum
      intro j hj
      exact _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixCosts.choose_le_cut (by have := Finset.mem_range.mp hj; omega) hhalf
    _ = _ := by simp

theorem downsetCap_add_one_le_layer {V cut : ℕ} (hhalf : cut ≤ V/2) :
    _root_.ThreeSum.SubsetAddress.downsetCap V cut+1 ≤ (V+2)*V.choose cut := by
  have hcut : cut ≤ V := hhalf.trans (Nat.div_le_self _ _)
  have hp := Nat.choose_pos hcut
  have hd := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixCosts.downsetCap_le_layer hhalf
  have hm := Nat.mul_le_mul_right (V.choose cut) (Nat.succ_le_succ hcut)
  nlinarith









end ThreeSum.ReportingHostSuffixCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Complete suffix-local querying from the physical global query mask

The host computes the local query mask by a bounded bit scan, reads the
lifting factor from its own power table, and executes the complete local-box
sparse query. No local-mask conversion or power table is supplied by a caller.
-/

namespace ThreeSum.LightReportingSuffixQueryHost
open _root_.ThreeSum.LightReportingSuffixQueryHost


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}









theorem time_bound {W V c t : ℕ} (hV : V ≤ W) (hc : c ≤ V) (ht : t ≤ c+1) :
    _root_.ThreeSum.LightReportingSuffixQueryHost.time W V c t ≤ 18000*(W+1)^3*(_root_.ThreeSum.LightSparseQuery.queryItems c t+1) := by
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixLower.time_bound hV
  have hq := _root_.ThreeSum.LightReportingSuffixQuery.time_bound hV hc ht
  have hp : (W+1)^2 ≤ (W+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hm : (W+1)^3 ≤ (W+1)^3*(_root_.ThreeSum.LightSparseQuery.queryItems c t+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hpos : 1 ≤ (W+1)^3*(_root_.ThreeSum.LightSparseQuery.queryItems c t+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold _root_.ThreeSum.LightReportingSuffixQueryHost.time
  nlinarith

end ThreeSum.LightReportingSuffixQueryHost

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

/-! # The actual physical-global-mask/local-box query returns the original raw prefix count -/

namespace ThreeSum.LightReportingSuffixQueryIndexed
open _root_.ThreeSum.LightReportingSuffixQueryIndexed


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
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]



theorem time_bound {h J k t : ℕ} (ht : t ≤ _root_.ThreeSum.LightBlockQuery.residualSize h J k+1) :
    _root_.ThreeSum.LightReportingSuffixQueryHost.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) (_root_.ThreeSum.LightBlockQuery.residualSize h J k) t ≤
      18000*(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)^3*(_root_.ThreeSum.LightSparseQuery.queryItems (_root_.ThreeSum.LightBlockQuery.residualSize h J k) t+1) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQueryHost.time_bound (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.suffixStage_le J (464*h) k)
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBoxes.residual_le_suffix ht

end ThreeSum.LightReportingSuffixQueryIndexed

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

theorem valueBound_le {W n : ℕ} (hn : n ≤ 2^(2*W)) :
    _root_.ThreeSum.LightReportingCatalogLookup.valueBound W n ≤ 2^(4*W+1) := by
  have hp : 0 < 2^(2*W) := Nat.two_pow_pos _
  have hn' : n+1 ≤ 2^(2*W+1) := by
    calc
      n+1 ≤ 2^(2*W)+2^(2*W) := by omega
      _ = 2^(2*W+1) := by ring
  calc
    _ ≤ 2^(2*W)*2^(2*W+1) := Nat.mul_le_mul_left _ hn'
    _ = 2^(4*W+1) := by rw [← pow_add]; congr 1; omega

theorem valueBound_add_one_le {W n : ℕ} (hn : n ≤ 2^(2*W)) :
    _root_.ThreeSum.LightReportingCatalogLookup.valueBound W n+1 ≤ 2^(4*W+2) := by
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogIndexCosts.valueBound_le hn
  have hp : 0 < 2^(4*W+1) := Nat.two_pow_pos _
  calc
    _ ≤ 2^(4*W+1)+2^(4*W+1) := by omega
    _ = 2^(4*W+2) := by ring

theorem remainder_log_le {W n : ℕ} (hn : n ≤ 2^(2*W)) :
    Nat.log 2 (_root_.ThreeSum.LightReportingCatalogLookup.valueBound W n+1) ≤ 4*W+2 :=
  (Nat.log_le_clog _ _).trans (Nat.clog_le_of_le_pow (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogIndexCosts.valueBound_add_one_le hn))



theorem lookup_time_le {W n : ℕ} (hn : n ≤ 2^(2*W)) :
    _root_.ThreeSum.LightReportingCatalogLookup.time W n ≤ 1000*(W+1) := by
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogIndexCosts.remainder_log_le hn
  unfold _root_.ThreeSum.LightReportingCatalogLookup.time _root_.Light.powTableTime _root_.ThreeSum.LightBandLookup.searchTime
  omega



theorem prefix_lookup_time_le {h J k : ℕ} (hk : k ≤ J) :
    _root_.ThreeSum.LightReportingCatalogLookup.time (J*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k) ≤
      1000*(J*(464*h)+1) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogIndexCosts.lookup_time_le (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.prefix_count_le_pow hk)



end ThreeSum.ReportingHostCatalogIndexCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual indexed suffix-box query with exact original raw-count semantics

The machine recovers the complete-catalog index from the two physical prefix
masks, reads its stored box pointer, and executes the suffix-local sparse
query. The original prefix is used only to state and prove its specification;
neither a catalog position nor a table pointer is supplied to this machine.
-/

namespace ThreeSum.LightReportingCatalogQuery
open _root_.ThreeSum.LightReportingCatalogQuery


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
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogSelection

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]









theorem time_bound {h J k t : ℕ} (hk : k ≤ J) (ht : t ≤ _root_.ThreeSum.LightBlockQuery.residualSize h J k+1) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery.time h J k t ≤
      20000*(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)^3*(_root_.ThreeSum.LightSparseQuery.queryItems (_root_.ThreeSum.LightBlockQuery.residualSize h J k) t+1) := by
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogIndexCosts.prefix_lookup_time_le (h := h) hk
  have hq := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQueryIndexed.time_bound (h := h) (J := J) (k := k) ht
  have hbase : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1 ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)^3 := Nat.le_self_pow (by omega) _
  have hm : (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)^3 ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)^3*(_root_.ThreeSum.LightSparseQuery.queryItems (_root_.ThreeSum.LightBlockQuery.residualSize h J k) t+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hpos : 1 ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)^3*(_root_.ThreeSum.LightSparseQuery.queryItems (_root_.ThreeSum.LightBlockQuery.residualSize h J k) t+1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  change _root_.ThreeSum.LightReportingCatalogLookup.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k) ≤ 1000*(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1) at hl
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery.time
  nlinarith

end ThreeSum.LightReportingCatalogQuery

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Polynomial overhead of the actual traversal operations

All logarithmic residue costs are bounded before the binomial work terms
are charged. This prevents an endpoint magnitude from being used as a
running-time bound. The final scalar overhead is polynomial in the block
dimensions and will therefore have exponent zero at the prescribed scales.
-/

namespace ThreeSum.SharedTraversalCosts
open _root_.ThreeSum.SharedTraversalCosts


open _root_.Finset
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000




theorem size_bounds (h J : ℕ) :
    1 ≤ _root_.ThreeSum.SharedTraversalCosts.size h J ∧ J+1 ≤ _root_.ThreeSum.SharedTraversalCosts.size h J ∧ 464*h+1 ≤ _root_.ThreeSum.SharedTraversalCosts.size h J ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1 ≤ _root_.ThreeSum.SharedTraversalCosts.size h J ∧
      1026*h+4 ≤ _root_.ThreeSum.SharedTraversalCosts.size h J ∧
      J*(464*h)+(514*h+2)*(J+1)+2 ≤ _root_.ThreeSum.SharedTraversalCosts.size h J := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> simp only [_root_.ThreeSum.SharedTraversalCosts.size,_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width] <;> nlinarith











theorem query_items_le_layer {c t : ℕ} (ht : t ≤ c/2) :
    _root_.ThreeSum.LightSparseQuery.queryItems c t+1 ≤ (c+2)*c.choose t := by
  have htc : t ≤ c := ht.trans (Nat.div_le_self _ _)
  simpa only [_root_.ThreeSum.LightSparseQuery.queryItems,_root_.ThreeSum.SubsetAddress.downsetCap,Nat.min_eq_left htc,_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ]
    using _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixCosts.downsetCap_add_one_le_layer ht

theorem residual_le_size (h J k : ℕ) : _root_.ThreeSum.LightBlockQuery.residualSize h J k+2 ≤ 2*_root_.ThreeSum.SharedTraversalCosts.size h J := by
  have hb := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.size_bounds h J).2.2.2.1
  have hr : _root_.ThreeSum.LightBlockQuery.residualSize h J k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J :=
    Nat.mul_le_mul (Nat.sub_le _ _) (by omega)
  omega





end ThreeSum.SharedTraversalCosts

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.SharedTraversalCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts

open _root_.Finset
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
section

theorem ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.initial_le_layer__implementation_ef29c26a05 {h J K : ℕ} (D : ℕ → _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostLevelData.Catalog) (hK : K ≤ J)
    (ht : (D 0).t ≤ _root_.ThreeSum.LightBlockQuery.residualSize h J 0/2) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.initialUnit h J D K ≤ _root_.ThreeSum.SharedTraversalCosts.overhead h J*(_root_.ThreeSum.LightBlockQuery.residualSize h J 0).choose (D 0).t := by
  let B := _root_.ThreeSum.SharedTraversalCosts.size h J
  let Q := (_root_.ThreeSum.LightBlockQuery.residualSize h J 0).choose (D 0).t
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.size_bounds h J
  have hB : B ≤ B^4 := Nat.le_self_pow (by decide) _
  have hq : 1 ≤ Q := Nat.choose_pos (ht.trans (Nat.div_le_self _ _))
  have hqitems := _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.query_items_le_layer ht
  have hqB := hqitems.trans (Nat.mul_le_mul_right Q (_root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.residual_le_size h J 0))
  have hquery := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery.time_bound (Nat.zero_le J)
    (by omega : (D 0).t ≤ residualSize h J 0+1)
  have hquery' : _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery.time h J 0 (D 0).t ≤ 40000*B^4*Q := by
    calc
      _ ≤ 20000*B^3*(2*B*Q) := hquery.trans (Nat.mul_le_mul
        (Nat.mul_le_mul_left 20000 (Nat.pow_le_pow_left hb.2.2.2.1 3)) hqB)
      _ = _ := by ring
  have hscalar : _root_.ThreeSum.LightBlockMasks.time J (464*h)+1300*K+3420 ≤ 5000*B := by
    unfold _root_.ThreeSum.LightBlockMasks.time _root_.Light.powTableTime
    have hh := hb.2.2.1
    have hj := hb.2.1
    omega
  have hs := hscalar.trans ((Nat.mul_le_mul_left 5000 hB).trans (Nat.le_mul_of_pos_right _ hq))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.initialUnit _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingWantedInitialize.time _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingInitializeStored.time
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingInitialize.time _root_.ThreeSum.LightDenseGuard.time _root_.ThreeSum.SharedTraversalCosts.overhead
  change _ ≤ 200000*B^4*Q
  nlinarith only [hquery',hs]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.initial_le_layer__implementation_ef29c26a05) := (@ThreeSum1960614.Machine.ThreeSum.SharedTraversalCosts.initial_le_layer__implementation_ef29c26a05)

#print axioms solution
