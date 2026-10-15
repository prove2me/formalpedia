-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:30:32.235258+00:00
-- url     : https://prove2.me/submissions/236d88c8-22af-48df-bb6a-b4e116094e8a

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
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
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
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
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
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
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
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
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
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
import Theorems.Thm_ThreeSum_SubsetAddress_enumerationWork_bound

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
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LightBlockChildren
end ThreeSum.LightBlockChildren
namespace ThreeSum.LightBlockChildrenIndexed
end ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightQueryEnumeration
end ThreeSum.LightQueryEnumeration
namespace ThreeSum.LightQueryWeights
end ThreeSum.LightQueryWeights
namespace ThreeSum.LightReportingCatalogBatch
end ThreeSum.LightReportingCatalogBatch
namespace ThreeSum.LightReportingCatalogExpand
end ThreeSum.LightReportingCatalogExpand
namespace ThreeSum.LightReportingCatalogLevel
end ThreeSum.LightReportingCatalogLevel
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
namespace ThreeSum.LightSubsetEnumeration
end ThreeSum.LightSubsetEnumeration
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostCatalogIndexCosts
end ThreeSum.ReportingHostCatalogIndexCosts
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostPackedCatalog
end ThreeSum.ReportingHostPackedCatalog
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
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
namespace ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
end ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockChildren
end ThreeSum1960614.Machine.ThreeSum.LightBlockChildren
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
end ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightQueryWeights
end ThreeSum1960614.Machine.ThreeSum.LightQueryWeights
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogBatch
end ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogBatch
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand
end ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel
end ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel
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
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.MaskErase
end ThreeSum1960614.Machine.ThreeSum.MaskErase
namespace ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
end ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
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
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
end ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

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
# Constructing the compact coordinate-weight table of a query mask

A width-sized scan tests each bit using the checked deletion routine and
appends the corresponding power of two. The output has one cell per set
bit, while the available buffer and scratch are only linear in the width.
-/

namespace ThreeSum.LightQueryWeights
open _root_.ThreeSum.LightQueryWeights


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.MaskErase
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

















theorem time_bound (W : ℕ) : _root_.ThreeSum.LightQueryWeights.time W ≤ 500*(W+1)^2 := by
  unfold _root_.ThreeSum.LightQueryWeights.time _root_.Light.powTableTime _root_.ThreeSum.LightMaskErase.time
  nlinarith

end ThreeSum.LightQueryWeights

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A complete output-sensitive subset enumerator inside an arbitrary query mask

The routine constructs its own compact coordinate weights, then invokes
the existing recursion on the number of selected coordinates. Every emitted
word is already a global mask; no ambient layer or Boolean cube is scanned.
-/

namespace ThreeSum.LightQueryEnumeration
open _root_.ThreeSum.LightQueryEnumeration


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}











theorem time_bound {W c t : ℕ} (hc : c ≤ W) :
    _root_.ThreeSum.LightQueryEnumeration.time W c t ≤ 1400*(W+1)^2*(c.choose t+1) := by
  have hbuild := _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryWeights.time_bound W
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.time_bound c t
  unfold _root_.ThreeSum.LightQueryEnumeration.time
  have hpoly : (4*c+1)*c.choose t+1 ≤ 4*(W+1)^2*(c.choose t+1) := by
    have hW : W+1 ≤ (W+1)^2 := by nlinarith
    nlinarith
  nlinarith [Nat.one_le_pow' 2 W]

end ThreeSum.LightQueryEnumeration

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual construction of every next-block reporting child

The fixed program enumerates the balanced subsets of the next block directly
in global coordinates. Two affine scans then write the exact left and right
prefix masks of every child, and subtraction returns the next residual mask.
All enumeration and scan execution is discharged by concrete procedures.
-/

namespace ThreeSum.LightBlockChildren
open _root_.ThreeSum.LightBlockChildren


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
open _root_.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}



















theorem time_bound {W c h : ℕ} (hc : c ≤ W) :
    _root_.ThreeSum.LightBlockChildren.time W c h ≤ 1600*(W+1)^2*(c.choose h+1) := by
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration.time_bound (t := h) hc
  have hpow : 1 ≤ (W+1)^2 := by nlinarith
  unfold _root_.ThreeSum.LightBlockChildren.time _root_.ThreeSum.LightReportingAffine.time
  nlinarith

end ThreeSum.LightBlockChildren

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

/-! # The concrete child constructor extends the original valid reporting prefixes -/

namespace ThreeSum.LightBlockChildrenIndexed
open _root_.ThreeSum.LightBlockChildrenIndexed


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockMaskLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}























theorem time_bound {h J k : ℕ} (hk : k < J) :
    _root_.ThreeSum.LightBlockChildren.time (J*(464*h)) (2*h) h ≤
      1600*(J*(464*h)+1)^2*(_root_.ThreeSum.LocalCoverBounds.groupSize h+1) := by
  apply _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildren.time_bound
  have hJ : 0 < J := by omega
  have hw : 464*h ≤ J*(464*h) := Nat.le_mul_of_pos_left _ hJ
  omega

end ThreeSum.LightBlockChildrenIndexed

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
# Actual raw-count batching through the physical suffix-box catalog

Each candidate supplies only its two constructed prefix masks. A real sorted
lookup chooses its cached suffix box, and the actual sparse query stores the
original raw prefix count. The catalog is shared and preserved by all calls.
-/

namespace ThreeSum.LightReportingCatalogBatch
open _root_.ThreeSum.LightReportingCatalogBatch


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
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog

set_option maxHeartbeats 2200000
set_option maxRecDepth 8000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]













theorem time_bound {h J k t n : ℕ} (hk : k ≤ J) (ht : t ≤ _root_.ThreeSum.LightBlockQuery.residualSize h J k+1) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogBatch.time h J k t n ≤
      21000*(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)^3*(_root_.ThreeSum.LightSparseQuery.queryItems (_root_.ThreeSum.LightBlockQuery.residualSize h J k) t+1)*(n+1) := by
  have hq := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogQuery.time_bound hk ht
  have hp : 1 ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)^3*(_root_.ThreeSum.LightSparseQuery.queryItems (_root_.ThreeSum.LightBlockQuery.residualSize h J k) t+1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogBatch.time
  nlinarith [Nat.mul_le_mul_left n hq]

end ThreeSum.LightReportingCatalogBatch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual shared-catalog queries followed by stable positive compaction -/

namespace ThreeSum.LightReportingCatalogLevel
open _root_.ThreeSum.LightReportingCatalogLevel


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
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]










theorem time_bound {h J k t n : ℕ} (hk : k ≤ J) (ht : t ≤ _root_.ThreeSum.LightBlockQuery.residualSize h J k+1) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel.time h J k t n ≤
      22000*(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)^3*(_root_.ThreeSum.LightSparseQuery.queryItems (_root_.ThreeSum.LightBlockQuery.residualSize h J k) t+1)*(n+1) := by
  have hq := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogBatch.time_bound (n := n) hk ht
  have hp : 1 ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)^3*(_root_.ThreeSum.LightSparseQuery.queryItems (_root_.ThreeSum.LightBlockQuery.residualSize h J k) t+1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel.time _root_.ThreeSum.LightReportingFilter.time
  nlinarith [Nat.mul_le_mul_right (n+1) hp]

end ThreeSum.LightReportingCatalogLevel

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockMaskLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockMaskLayout
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
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.time_bound__implementation_ac4889bea2 {h J k t : ℕ} (hk : k < J) (ht : t ≤ _root_.ThreeSum.LightBlockQuery.residualSize h J (k+1)+1) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.time h J k t ≤
      25000*(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)^3*(_root_.ThreeSum.LightSparseQuery.queryItems (_root_.ThreeSum.LightBlockQuery.residualSize h J (k+1)) t+1)*(_root_.ThreeSum.LocalCoverBounds.groupSize h+1) := by
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildrenIndexed.time_bound (h := h) hk
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel.time_bound (n := _root_.ThreeSum.LocalCoverBounds.groupSize h) (Nat.succ_le_of_lt hk) ht
  have hp : (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)^2 ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hm : (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)^2*(_root_.ThreeSum.LocalCoverBounds.groupSize h+1) ≤
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)^3*(_root_.ThreeSum.LightSparseQuery.queryItems (_root_.ThreeSum.LightBlockQuery.residualSize h J (k+1)) t+1)*(_root_.ThreeSum.LocalCoverBounds.groupSize h+1) := by
    nlinarith [Nat.mul_le_mul_right (_root_.ThreeSum.LocalCoverBounds.groupSize h+1) hp]
  have hpos : 1 ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)^3*(_root_.ThreeSum.LightSparseQuery.queryItems (_root_.ThreeSum.LightBlockQuery.residualSize h J (k+1)) t+1)*(_root_.ThreeSum.LocalCoverBounds.groupSize h+1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  change _root_.ThreeSum.LightBlockChildren.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (2*h) h ≤ 1600*(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)^2*(_root_.ThreeSum.LocalCoverBounds.groupSize h+1) at hc
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.time
  nlinarith
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.time_bound__implementation_ac4889bea2) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogExpand.time_bound__implementation_ac4889bea2)

#print axioms solution
