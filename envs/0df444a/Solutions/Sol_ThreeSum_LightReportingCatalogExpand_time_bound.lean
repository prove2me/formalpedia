-- Prove2me | solution 1 for ThreeSum.LightReportingCatalogExpand.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:39:20.941703+00:00
-- url     : https://prove2.me/submissions/6ff37e7b-7144-4400-8682-c8462ef6d003

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
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
import Mathlib.Algebra.Order.Field.Basic
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
import Mathlib.Data.Int.Cast.Lemmas
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
import Mathlib.Data.Nat.Cast.Order.Ring
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
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_LightReportingSuffixQuery_time_bound
import Theorems.Thm_ThreeSum_SubsetAddress_enumerationWork_bound


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
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
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockChildrenIndexed
end ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostCatalogSelection
end ThreeSum.ReportingHostCatalogSelection
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostPrefixCatalog
end ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Exact bridge from row-major machine masks to the block reporting query

The explicit coordinate equivalence sends the remaining blocks to a
contiguous suffix. Transport of finite subset sums identifies the machine's
Möbius value with the concrete forced-prefix count used by reporting.
-/

namespace ThreeSum.BlockIndexedQuery

open Finset BlockRows BlockIndex BlockForced BlockEncoding GlobalEncoding
open LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open scoped BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false







theorem suffixStage_le (J L k : ℕ) : suffixStage J L k ≤ J*L :=
  Nat.mul_le_mul_right L (Nat.sub_le _ _)






















































































section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]






































































end Histograms

end ThreeSum.BlockIndexedQuery

end

section


/-!
# Output-sensitive subset-layer enumeration in the benchmark language

The recursive routine writes into consecutive output cells. Empty layers
return immediately; a zero-cardinality layer emits one mask. The two
recursive children share the output buffer and write adjacent, disjoint
segments. No ambient Boolean cube is scanned and no output list is copied.
-/

namespace ThreeSum.LightSubsetEnumeration

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}












































theorem time_bound (L k : ℕ) :
    time L k ≤ 150*((4*L+1)*L.choose k+1) := by
  exact Nat.mul_le_mul_left 150 (enumerationWork_bound L k)



























































































































































end ThreeSum.LightSubsetEnumeration

end

section


/-!
# Constructing the compact coordinate-weight table of a query mask

A width-sized scan tests each bit using the checked deletion routine and
appends the corresponding power of two. The output has one cell per set
bit, while the available buffer and scratch are only linear in the width.
-/

namespace ThreeSum.LightQueryWeights

open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
open QueryCoordinates

variable {lim : Limits} {P : Program}























































































































































theorem time_bound (W : ℕ) : time W ≤ 500*(W+1)^2 := by
  unfold time powTableTime LightMaskErase.time
  nlinarith

end ThreeSum.LightQueryWeights

end

section


/-!
# A complete output-sensitive subset enumerator inside an arbitrary query mask

The routine constructs its own compact coordinate weights, then invokes
the existing recursion on the number of selected coordinates. Every emitted
word is already a global mask; no ambient layer or Boolean cube is scanned.
-/

namespace ThreeSum.LightQueryEnumeration

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress QueryCoordinates

variable {lim : Limits} {P : Program}












































































theorem time_bound {W c t : ℕ} (hc : c ≤ W) :
    time W c t ≤ 1400*(W+1)^2*(c.choose t+1) := by
  have hbuild := LightQueryWeights.time_bound W
  have he := LightSubsetEnumeration.time_bound c t
  unfold time
  have hpoly : (4*c+1)*c.choose t+1 ≤ 4*(W+1)^2*(c.choose t+1) := by
    have hW : W+1 ≤ (W+1)^2 := by nlinarith
    nlinarith
  nlinarith [Nat.one_le_pow' 2 W]

end ThreeSum.LightQueryEnumeration

end

section


/-!
# Actual construction of every next-block reporting child

The fixed program enumerates the balanced subsets of the next block directly
in global coordinates. Two affine scans then write the exact left and right
prefix masks of every child, and subtraction returns the next residual mask.
All enumeration and scan execution is discharged by concrete procedures.
-/

namespace ThreeSum.LightBlockChildren

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open QueryCoordinates ReportingHostMasks

variable {lim : Limits} {P : Program}





























































































































































theorem time_bound {W c h : ℕ} (hc : c ≤ W) :
    time W c h ≤ 1600*(W+1)^2*(c.choose h+1) := by
  have he := LightQueryEnumeration.time_bound (t := h) hc
  have hpow : 1 ≤ (W+1)^2 := by nlinarith
  unfold time LightReportingAffine.time
  nlinarith

end ThreeSum.LightBlockChildren

end

section


/-! # The concrete child constructor extends the original valid reporting prefixes -/

namespace ThreeSum.LightBlockChildrenIndexed

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open BlockRows BlockIndex BlockMaskLayout BlockIndexedQuery BlockForced StoredReporting
open ReportingHostMasks QueryCoordinates GlobalEncoding LocalCoverBounds

variable {lim : Limits}































































































































theorem time_bound {h J k : ℕ} (hk : k < J) :
    LightBlockChildren.time (J*(512*h)) (2*h) h ≤
      1600*(J*(512*h)+1)^2*(groupSize h+1) := by
  apply LightBlockChildren.time_bound
  have hJ : 0 < J := by omega
  have hw : 512*h ≤ J*(512*h) := Nat.le_mul_of_pos_left _ hJ
  omega

end ThreeSum.LightBlockChildrenIndexed

end

section


/-! # Actual shrinking-suffix box preprocessing for an original valid block prefix -/

namespace ThreeSum.LightReportingSuffixBoxes

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds LightBlockQuery ReportingHostSuffix

variable {lim : Limits}
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]








theorem residual_le_suffix {h J k : ℕ} : residualSize h J k ≤ suffixStage J (512*h) k := by
  exact Nat.mul_le_mul_left (J-k) (by omega)






























































end ThreeSum.LightReportingSuffixBoxes

end

section


/-!
# Exact sorted lookup of a prefix catalog record

Each original catalog position is retained as the low digit of a packed
integer. A sorted search uses the upper end of the requested key's interval;
the unique prefix-key proof forces that hit to be the original record, and
remainder recovers its unchanged catalog index.
-/

namespace ThreeSum.ReportingHostPackedCatalog

open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPrefixOrder

set_option maxHeartbeats 600000






















































































































theorem prefix_count_le_pow {h J k : ℕ} (hk : k ≤ J) :
    LightReportingPrefixCatalog.count h k ≤ 2^(2*(J*(512*h))) := by
  have hhalf : 2*h ≤ 512*h := by omega
  have he : LightReportingPrefixArrays.localCount (512*h) h ≤ 2^(2*(512*h)) := by
    calc
      _ ≤ 2^(512*h)*2^(2*h) := Nat.mul_le_mul (Nat.choose_le_two_pow _ _) (Nat.choose_le_two_pow _ _)
      _ ≤ 2^(512*h)*2^(512*h) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hhalf)
      _ = 2^(2*(512*h)) := by rw [← pow_add]; congr 1; omega
  calc
    _ ≤ (2^(2*(512*h)))^k := Nat.pow_le_pow_left he k
    _ = 2^(2*(k*(512*h))) := by rw [← pow_mul]; congr 1; ring
    _ ≤ 2^(2*(J*(512*h))) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hk))

end ThreeSum.ReportingHostPackedCatalog

end

section


/-!
# Actual global-to-local suffix-mask conversion

The program constructs powers once, tests each suffix coordinate using the
verified mask-bit procedure, and accumulates its local power. Runtime is
quadratic in the width, independent of the numeric mask value.
-/

namespace ThreeSum.LightReportingSuffixLower

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open ReportingHostSuffix MaskErase

variable {lim : Limits} {P : Program}








































































































































theorem time_bound {W V : ℕ} (hV : V ≤ W) : time W V ≤ 400*(W+1)^2 := by
  have hm := Nat.mul_le_mul_right (LightMaskErase.time W+100) hV
  unfold time powTableTime LightMaskErase.time at *
  nlinarith

end ThreeSum.LightReportingSuffixLower

end

section


/-!
# Complete suffix-local querying from the physical global query mask

The host computes the local query mask by a bounded bit scan, reads the
lifting factor from its own power table, and executes the complete local-box
sparse query. No local-mask conversion or power table is supplied by a caller.
-/

namespace ThreeSum.LightReportingSuffixQueryHost

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix

variable {lim : Limits}









































































theorem time_bound {W V c t : ℕ} (hV : V ≤ W) (hc : c ≤ V) (ht : t ≤ c+1) :
    time W V c t ≤ 18000*(W+1)^3*(LightSparseQuery.queryItems c t+1) := by
  have hl := LightReportingSuffixLower.time_bound hV
  have hq := LightReportingSuffixQuery.time_bound hV hc ht
  have hp : (W+1)^2 ≤ (W+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hm : (W+1)^3 ≤ (W+1)^3*(LightSparseQuery.queryItems c t+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hpos : 1 ≤ (W+1)^3*(LightSparseQuery.queryItems c t+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold time
  nlinarith

end ThreeSum.LightReportingSuffixQueryHost

end

section


/-! # The actual physical-global-mask/local-box query returns the original raw prefix count -/

namespace ThreeSum.LightReportingSuffixQueryIndexed

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

































































theorem time_bound {h J k t : ℕ} (ht : t ≤ residualSize h J k+1) :
    LightReportingSuffixQueryHost.time (width h J) (suffixStage J (512*h) k) (residualSize h J k) t ≤
      18000*(width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J k) t+1) :=
  LightReportingSuffixQueryHost.time_bound (suffixStage_le J (512*h) k)
    LightReportingSuffixBoxes.residual_le_suffix ht

end ThreeSum.LightReportingSuffixQueryIndexed

end

section


/-!
# The actual sorted index stays within polynomial mask-width overhead

Complete prefix catalogs have at most 2^(2W) records. This bounds both the
merge-sort logarithm and the binary-remainder scratch/time by the mask width,
so lookup contributes no linear factor in the catalog size to a query.
-/

namespace ThreeSum.ReportingHostCatalogIndexCosts

open Light ThreeSum.LightPascal

set_option maxHeartbeats 300000

theorem valueBound_le {W n : ℕ} (hn : n ≤ 2^(2*W)) :
    LightReportingCatalogLookup.valueBound W n ≤ 2^(4*W+1) := by
  have hp : 0 < 2^(2*W) := Nat.two_pow_pos _
  have hn' : n+1 ≤ 2^(2*W+1) := by
    calc
      n+1 ≤ 2^(2*W)+2^(2*W) := by omega
      _ = 2^(2*W+1) := by ring
  calc
    _ ≤ 2^(2*W)*2^(2*W+1) := Nat.mul_le_mul_left _ hn'
    _ = 2^(4*W+1) := by rw [← pow_add]; congr 1; omega

theorem valueBound_add_one_le {W n : ℕ} (hn : n ≤ 2^(2*W)) :
    LightReportingCatalogLookup.valueBound W n+1 ≤ 2^(4*W+2) := by
  have hb := valueBound_le hn
  have hp : 0 < 2^(4*W+1) := Nat.two_pow_pos _
  calc
    _ ≤ 2^(4*W+1)+2^(4*W+1) := by omega
    _ = 2^(4*W+2) := by ring

theorem remainder_log_le {W n : ℕ} (hn : n ≤ 2^(2*W)) :
    Nat.log 2 (LightReportingCatalogLookup.valueBound W n+1) ≤ 4*W+2 :=
  (Nat.log_le_clog _ _).trans (Nat.clog_le_of_le_pow (valueBound_add_one_le hn))




theorem lookup_time_le {W n : ℕ} (hn : n ≤ 2^(2*W)) :
    LightReportingCatalogLookup.time W n ≤ 1000*(W+1) := by
  have hh := remainder_log_le hn
  unfold LightReportingCatalogLookup.time powTableTime LightBandLookup.searchTime
  omega








theorem prefix_lookup_time_le {h J k : ℕ} (hk : k ≤ J) :
    LightReportingCatalogLookup.time (J*(512*h)) (LightReportingPrefixCatalog.count h k) ≤
      1000*(J*(512*h)+1) :=
  lookup_time_le (ReportingHostPackedCatalog.prefix_count_le_pow hk)






end ThreeSum.ReportingHostCatalogIndexCosts

end

section


/-!
# Actual indexed suffix-box query with exact original raw-count semantics

The machine recovers the complete-catalog index from the two physical prefix
masks, reads its stored box pointer, and executes the suffix-local sparse
query. The original prefix is used only to state and prove its specification;
neither a catalog position nor a table pointer is supplied to this machine.
-/

namespace ThreeSum.LightReportingCatalogQuery

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixCatalog ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostCatalogSelection

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]








































































































theorem time_bound {h J k t : ℕ} (hk : k ≤ J) (ht : t ≤ residualSize h J k+1) :
    time h J k t ≤
      20000*(width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J k) t+1) := by
  have hl := ReportingHostCatalogIndexCosts.prefix_lookup_time_le (h := h) hk
  have hq := LightReportingSuffixQueryIndexed.time_bound (h := h) (J := J) (k := k) ht
  have hbase : width h J+1 ≤ (width h J+1)^3 := Nat.le_self_pow (by omega) _
  have hm : (width h J+1)^3 ≤ (width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J k) t+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hpos : 1 ≤ (width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J k) t+1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  change LightReportingCatalogLookup.time (width h J) (count h k) ≤ 1000*(width h J+1) at hl
  unfold time
  nlinarith

end ThreeSum.LightReportingCatalogQuery

end

section


/-!
# Actual raw-count batching through the physical suffix-box catalog

Each candidate supplies only its two constructed prefix masks. A real sorted
lookup chooses its cached suffix box, and the actual sparse query stores the
original raw prefix count. The catalog is shared and preserved by all calls.
-/

namespace ThreeSum.LightReportingCatalogBatch

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog

set_option maxHeartbeats 2200000
set_option maxRecDepth 8000

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]


































































































































































theorem time_bound {h J k t n : ℕ} (hk : k ≤ J) (ht : t ≤ residualSize h J k+1) :
    time h J k t n ≤
      21000*(width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J k) t+1)*(n+1) := by
  have hq := LightReportingCatalogQuery.time_bound hk ht
  have hp : 1 ≤ (width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J k) t+1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold time
  nlinarith [Nat.mul_le_mul_left n hq]

end ThreeSum.LightReportingCatalogBatch

end

section


/-! # Actual shared-catalog queries followed by stable positive compaction -/

namespace ThreeSum.LightReportingCatalogLevel

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]


























































































theorem time_bound {h J k t n : ℕ} (hk : k ≤ J) (ht : t ≤ residualSize h J k+1) :
    time h J k t n ≤
      22000*(width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J k) t+1)*(n+1) := by
  have hq := LightReportingCatalogBatch.time_bound (n := n) hk ht
  have hp : 1 ≤ (width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J k) t+1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold time LightReportingFilter.time
  nlinarith [Nat.mul_le_mul_right (n+1) hp]

end ThreeSum.LightReportingCatalogLevel

end

section


/-!
# Complete parent expansion through an actual shared shrinking-suffix catalog

This program constructs every ordered child mask pair, locates its own cached
box through the physical sorted index, runs the exact original raw-count
query, and stably compacts positive child positions. It requires no supplied
per-child box addresses and retains the complete source/catalog storage.
-/

namespace ThreeSum.LightReportingCatalogExpand

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockIndex BlockMaskLayout BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
open ReportingHostMasks LightBlockChildrenIndexed

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

















































































































































theorem time_bound_sourceProof {h J k t : ℕ} (hk : k < J) (ht : t ≤ residualSize h J (k+1)+1) :
    time h J k t ≤
      25000*(width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J (k+1)) t+1)*(groupSize h+1) := by
  have hc := LightBlockChildrenIndexed.time_bound (h := h) hk
  have hl := LightReportingCatalogLevel.time_bound (n := groupSize h) (Nat.succ_le_of_lt hk) ht
  have hp : (width h J+1)^2 ≤ (width h J+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hm : (width h J+1)^2*(groupSize h+1) ≤
      (width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J (k+1)) t+1)*(groupSize h+1) := by
    nlinarith [Nat.mul_le_mul_right (groupSize h+1) hp]
  have hpos : 1 ≤ (width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J (k+1)) t+1)*(groupSize h+1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  change LightBlockChildren.time (width h J) (2*h) h ≤ 1600*(width h J+1)^2*(groupSize h+1) at hc
  unfold time
  nlinarith

end ThreeSum.LightReportingCatalogExpand

end


theorem solution : ∀ {h J k t : Nat},
  @LT.lt.{0} Nat instLTNat k J →
    @LE.le.{0} Nat instLENat t
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (ThreeSum.LightBlockQuery.residualSize h J
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      @LE.le.{0} Nat instLENat (ThreeSum.LightReportingCatalogExpand.time h J k t)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 25000) (instOfNatNat (nat_lit 25000)))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.LightBlockQuery.width h J)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (ThreeSum.LightSparseQuery.queryItems
                (ThreeSum.LightBlockQuery.residualSize h J
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                t)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.LocalCoverBounds.groupSize h)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  exact @ThreeSum.LightReportingCatalogExpand.time_bound_sourceProof

#print axioms solution
