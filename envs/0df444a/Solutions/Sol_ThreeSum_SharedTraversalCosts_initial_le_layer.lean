-- Prove2me | solution 1 for ThreeSum.SharedTraversalCosts.initial_le_layer
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:39:25.832843+00:00
-- url     : https://prove2.me/submissions/adf05efa-43d4-4d16-827d-760ee673ffc2

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
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
import Mathlib.Algebra.Order.Field.Basic
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
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
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
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
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_LightReportingSuffixQuery_time_bound


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
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
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
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostCatalogSelection
end ThreeSum.ReportingHostCatalogSelection
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
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
# Compact addresses for bounded-cardinality bit masks

Both ranking and enumeration recurse on the highest available bit. The
enumerator stops immediately when the requested layer is empty. In
particular, it does not enumerate the ambient Boolean cube and filter it.
-/

namespace ThreeSum.SubsetAddress

set_option maxRecDepth 4000

open Finset
open scoped BigOperators









































































































































































































































theorem layerOffset_succ (L k : ℕ) :
    layerOffset L (k + 1) = layerOffset L k + L.choose k := by
  exact Finset.sum_range_succ _ _

























































































































































































































end ThreeSum.SubsetAddress

end

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


/-! # The actual local box construction is charged to the suffix binomial layer -/

namespace ThreeSum.ReportingHostSuffixCosts

open ThreeSum.SubsetAddress ThreeSum.LightBlockQuery ThreeSum.BlockIndexedQuery
open scoped BigOperators

theorem choose_le_cut {V j cut : ℕ} (hj : j ≤ cut) (hhalf : cut ≤ V/2) :
    V.choose j ≤ V.choose cut := by
  induction cut,hj using Nat.le_induction with
  | base => exact le_rfl
  | succ cut hj ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem downsetCap_le_layer {V cut : ℕ} (hhalf : cut ≤ V/2) :
    downsetCap V cut ≤ (cut+1)*V.choose cut := by
  have hcut : cut ≤ V := hhalf.trans (Nat.div_le_self _ _)
  simp only [downsetCap,Nat.min_eq_left hcut,layerOffset]
  calc
    _ ≤ ∑ _j ∈ Finset.range (cut+1), V.choose cut := by
      apply Finset.sum_le_sum
      intro j hj
      exact choose_le_cut (by have := Finset.mem_range.mp hj; omega) hhalf
    _ = _ := by simp

theorem downsetCap_add_one_le_layer {V cut : ℕ} (hhalf : cut ≤ V/2) :
    downsetCap V cut+1 ≤ (V+2)*V.choose cut := by
  have hcut : cut ≤ V := hhalf.trans (Nat.div_le_self _ _)
  have hp := Nat.choose_pos hcut
  have hd := downsetCap_le_layer hhalf
  have hm := Nat.mul_le_mul_right (V.choose cut) (Nat.succ_le_succ hcut)
  nlinarith







































end ThreeSum.ReportingHostSuffixCosts

end

section


/-!
# Polynomial overhead of the actual traversal operations

All logarithmic residue costs are bounded before the binomial work terms
are charged. This prevents an endpoint magnitude from being used as a
running-time bound. The final scalar overhead is polynomial in the block
dimensions and will therefore have exponent zero at the prescribed scales.
-/

namespace ThreeSum.SharedTraversalCosts

open Finset Light LocalCoverBounds LightBlockQuery ReportingHostLevelData
open SubsetAddress
open scoped BigOperators

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000




theorem size_bounds (h J : ℕ) :
    1 ≤ size h J ∧ J+1 ≤ size h J ∧ 512*h+1 ≤ size h J ∧
      width h J+1 ≤ size h J ∧
      1026*h+4 ≤ size h J ∧
      J*(512*h)+(514*h+2)*(J+1)+2 ≤ size h J := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> simp only [size,width] <;> nlinarith






















































































































theorem query_items_le_layer {c t : ℕ} (ht : t ≤ c/2) :
    LightSparseQuery.queryItems c t+1 ≤ (c+2)*c.choose t := by
  have htc : t ≤ c := ht.trans (Nat.div_le_self _ _)
  simpa only [LightSparseQuery.queryItems,downsetCap,Nat.min_eq_left htc,layerOffset_succ]
    using ReportingHostSuffixCosts.downsetCap_add_one_le_layer ht

theorem residual_le_size (h J k : ℕ) : residualSize h J k+2 ≤ 2*size h J := by
  have hb := (size_bounds h J).2.2.2.1
  have hr : residualSize h J k ≤ width h J :=
    Nat.mul_le_mul (Nat.sub_le _ _) (by omega)
  omega

























theorem initial_le_layer_sourceProof {h J K : ℕ} (D : ℕ → Catalog) (hK : K ≤ J)
    (ht : (D 0).t ≤ residualSize h J 0/2) :
    initialUnit h J D K ≤ overhead h J*(residualSize h J 0).choose (D 0).t := by
  let B := size h J
  let Q := (residualSize h J 0).choose (D 0).t
  have hb := size_bounds h J
  have hB : B ≤ B^4 := Nat.le_self_pow (by decide) _
  have hq : 1 ≤ Q := Nat.choose_pos (ht.trans (Nat.div_le_self _ _))
  have hqitems := query_items_le_layer ht
  have hqB := hqitems.trans (Nat.mul_le_mul_right Q (residual_le_size h J 0))
  have hquery := LightReportingCatalogQuery.time_bound (Nat.zero_le J)
    (by omega : (D 0).t ≤ residualSize h J 0+1)
  have hquery' : LightReportingCatalogQuery.time h J 0 (D 0).t ≤ 40000*B^4*Q := by
    calc
      _ ≤ 20000*B^3*(2*B*Q) := hquery.trans (Nat.mul_le_mul
        (Nat.mul_le_mul_left 20000 (Nat.pow_le_pow_left hb.2.2.2.1 3)) hqB)
      _ = _ := by ring
  have hscalar : LightBlockMasks.time J (512*h)+1300*K+3420 ≤ 5000*B := by
    unfold LightBlockMasks.time powTableTime
    have hh := hb.2.2.1
    have hj := hb.2.1
    omega
  have hs := hscalar.trans ((Nat.mul_le_mul_left 5000 hB).trans (Nat.le_mul_of_pos_right _ hq))
  unfold initialUnit LightReportingWantedInitialize.time LightReportingInitializeStored.time
    LightReportingInitialize.time LightDenseGuard.time overhead
  change _ ≤ 200000*B^4*Q
  nlinarith only [hquery',hs]

end ThreeSum.SharedTraversalCosts

end


theorem solution : ∀ {h J K : Nat} (D : Nat → ThreeSum.ReportingHostLevelData.Catalog),
  @LE.le.{0} Nat instLENat K J →
    @LE.le.{0} Nat instLENat (D (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).t
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
          (ThreeSum.LightBlockQuery.residualSize h J (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
      @LE.le.{0} Nat instLENat (ThreeSum.SharedTraversalCosts.initialUnit h J D K)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.SharedTraversalCosts.overhead h J)
          ((ThreeSum.LightBlockQuery.residualSize h J
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).choose
            (D (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).t)) := by
  exact @ThreeSum.SharedTraversalCosts.initial_le_layer_sourceProof

#print axioms solution
