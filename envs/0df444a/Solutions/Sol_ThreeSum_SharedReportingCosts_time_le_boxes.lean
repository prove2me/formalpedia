-- Prove2me | solution 1 for ThreeSum.SharedReportingCosts.time_le_boxes
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:07:01.888872+00:00
-- url     : https://prove2.me/submissions/7ed9a66c-8a09-41ef-9959-01255ca7327c

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
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
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
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
import Theorems.Thm_ThreeSum_LayerCounts_edgeSet_card
import Theorems.Thm_ThreeSum_LightRadixKeys_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixCatalogSetup_time_bound
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
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LayerCounts
end ThreeSum.LayerCounts
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.ReportingHostPackedCatalog
end ThreeSum.ReportingHostPackedCatalog
namespace ThreeSum.ReportingHostPairEnumeration
end ThreeSum.ReportingHostPairEnumeration
namespace ThreeSum.ReportingHostPairSegments
end ThreeSum.ReportingHostPairSegments
namespace ThreeSum.ReportingHostPrefixCatalog
end ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.ReportingHostSuffixCosts
end ThreeSum.ReportingHostSuffixCosts
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.Switch
end ThreeSum.Switch

section


/-!
# Exact counts for the local subset graph

These are counts of the executable finite sets used by the graph, rather
than abstract numerical cardinality hypotheses.  An edge is an ordered
pair of disjoint `h`-subsets of `Fin L`.
-/

namespace ThreeSum.LayerCounts

open Finset


























































































theorem vertex_degree_identity (L h : ℕ) :
    L.choose h * (L - h).choose h = L.choose (2 * h) * (2 * h).choose h := by
  simpa [show 2 * h - h = h by omega] using
    (Nat.choose_mul (n := L) (k := 2 * h) (s := h) (by omega)).symm

















end ThreeSum.LayerCounts

end

section


/-!
# The concrete local subset graph and its binary words

A left vertex has ones exactly on its `h`-subset.  A right vertex has zeros
exactly on its `h`-subset.  The endpoint maps, their separation, and the
equality mask are proved directly from finite-set membership.
-/

namespace ThreeSum.LocalGraph

variable {α : Type*} [DecidableEq α]
























































section ConcreteGraph

open LayerCounts




variable {L h : ℕ}












































































theorem edge_card (L h : ℕ) :
    Fintype.card (Edge L h) = L.choose (2 * h) * (2 * h).choose h := by
  rw [Fintype.card_coe, edgeSet_card]







































end ConcreteGraph

end ThreeSum.LocalGraph

end

section


/-!
# Actual finite hierarchy counts

These are the binomial counts used by the concrete microblock hierarchy.
Every prefix partition is included.  The integer switch and its rounding
allowance are applied before any asymptotic estimate is made.  The counts
in this module are combinatorial work counts; the implementation's operation
counts, raw wanted incidences, and false-mass bounds are separate interfaces.
-/

namespace ThreeSum.CostLedger

open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch
open scoped Topology BigOperators

set_option maxHeartbeats 400000


































theorem microOutputs_pos (n : ℕ) : 0 < microOutputs n :=
  Nat.choose_pos (by omega)

theorem microPartitions_pos (n : ℕ) : 0 < microPartitions n :=
  Nat.choose_pos (Nat.div_le_self _ _)

theorem prefixChoices_pos (n j : ℕ) : 0 < prefixChoices n j :=
  Nat.pow_pos (Nat.mul_pos (microOutputs_pos n) (microPartitions_pos n))

theorem suffixBoxes_pos (n j : ℕ) : 0 < suffixBoxes n j :=
  Nat.choose_pos (by omega)

theorem prefixBoxes_pos (n j : ℕ) : 0 < prefixBoxes n j :=
  Nat.mul_pos (prefixChoices_pos n j) (suffixBoxes_pos n j)

noncomputable section

















































































































































end
end ThreeSum.CostLedger

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
# A fixed subset-layer enumerator with its own power-table construction

The main theorem has no supplied lookup-table correctness assumption. The
only auxiliary memory is a table of `L+1` powers of two, built once before
the recursive enumeration. The output has exactly `L.choose k` cells.
-/

namespace ThreeSum.LightSubsetEnumerationSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}


































































theorem time_bound (L k : ℕ) : time L k ≤ 800*(L+1)*(L.choose k+1) := by
  have h := LightSubsetEnumeration.time_bound L k
  unfold time powTableTime
  nlinarith

end ThreeSum.LightSubsetEnumerationSetup

end

section


/-!
# Exact prefix catalog keys and sharing for fixed source occurrences

A catalog key consists only of the first k ordered disjoint balanced row
pairs. Its exact cardinality is (microOutputs*microPartitions)^k. Neither the
remaining output rows nor the wanted A-index enter a local box table once
the global occurrence vector is fixed.
-/

namespace ThreeSum.ReportingHostPrefixCatalog

open Finset LocalGraph LayerCounts BlockRows BlockIndex BlockIndexedQuery
open BlockEncoding BlockForced GlobalEncoding StoredReporting ReportingHostSuffix

set_option linter.unusedSectionVars false



theorem prefix_card (h k : ℕ) :
    Fintype.card (Prefix h k) = ((512*h).choose (2*h)*(2*h).choose h)^k := by
  simp only [Prefix,Fintype.card_fun,Fintype.card_fin,LocalGraph.edge_card]




























































section Sources

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

















































end Sources

end ThreeSum.ReportingHostPrefixCatalog

end

section


/-!
# Actual direct construction of all local balanced row pairs

An own-power layer enumerator constructs the left subsets. For each left
subset, an actual output-sensitive query enumerator constructs its disjoint
right subsets, and an affine pass writes the matching repeated left mask.
-/

namespace ThreeSum.LightReportingPairRows

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPairEnumeration

set_option maxHeartbeats 1800000

variable {lim : Limits}



































































































































































theorem time_bound {L h : ℕ} (hh : 2*h ≤ L) :
    time L h ≤ 4000*(L+1)^2*(L.choose (2*h)*(2*h).choose h+1) := by
  have hdeg : 0 < (L-h).choose h := Nat.choose_pos (by omega)
  have hs := LightSubsetEnumerationSetup.time_bound L h
  have hq := LightQueryEnumeration.time_bound (t := h) (Nat.sub_le L h)
  have hlinear : L+1 ≤ (L+1)^2 := by nlinarith
  have hv : L.choose h ≤ L.choose h*(L-h).choose h := Nat.le_mul_of_pos_right _ hdeg
  have hm := Nat.mul_le_mul_left (L.choose h) hq
  rw [← LayerCounts.vertex_degree_identity]
  unfold time roundTime LightReportingAffine.time
  nlinarith

end ThreeSum.LightReportingPairRows

end

section


/-!
# Constructing both complete prefix-mask product arrays in the same record order

The local pair arrays are built directly, then the verified positional-key
host is used twice with radix 2^L. Both results share the literal tuple order,
including separate entries for pairs with equal left or right projections.
-/

namespace ThreeSum.LightReportingPrefixArrays

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPairEnumeration ReportingHostPairSegments

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000

variable {lim : Limits}










































































































theorem time_bound {L h k : ℕ} (hh : 2*h ≤ L) :
    time L h k ≤ 5000*(L+1)^2*(localCount L h+1)+
      600*(k+1)*((localCount L h)^k+1)+300 := by
  have hp := LightReportingPairRows.time_bound hh
  have hk := LightRadixKeys.time_bound (localCount L h) k
    (Nat.one_le_of_lt (Nat.mul_pos (Nat.choose_pos hh) (Nat.choose_pos (by omega))))
  unfold time powTableTime
  change LightReportingPairRows.time L h ≤ 4000*(L+1)^2*(localCount L h+1) at hp
  nlinarith

end ThreeSum.LightReportingPrefixArrays

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
# Actual packed-key construction and sorted catalog index

The powers table supplies the physical mask radix. A linear pass retains the
original catalog index as a low digit, and the benchmark's verified merge
sort orders these records without changing their multiplicity or payload.
-/

namespace ThreeSum.LightReportingSortedCatalog

open Light ThreeSum.LightPascal ThreeSum.LightSubsetAddress ReportingHostPackedCatalog

variable {lim : Limits}








































































theorem time_bound (W n : ℕ) : time W n ≤ 200*(W+1)+200*(n+1)*(Nat.clog 2 n+1) := by
  unfold time powTableTime LightReportingPackKeys.time sortTime
  have hh : n-1 ≤ n := Nat.sub_le _ _
  nlinarith

end ThreeSum.LightReportingSortedCatalog

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





















theorem suffix_width_eq (h J k : ℕ) :
    suffixStage J (512*h) k = 256*residualSize h J k := by
  unfold suffixStage residualSize
  ring














end ThreeSum.ReportingHostSuffixCosts

end

section


/-!
# Charging the actual shared suffix catalog to the original finite ledger

The bound uses the exact physically constructed local table size and the
proved full prefix-key cardinality. Physical enumeration and lookup of those
prefix keys remain separate executable components.
-/

namespace ThreeSum.ReportingHostCatalogCosts

set_option maxRecDepth 8000

open ThreeSum.SubsetAddress ThreeSum.LightBlockQuery ThreeSum.BlockIndexedQuery
open ReportingHostPrefixCatalog ReportingHostSuffixCosts

theorem prefix_card_pos (h k : ℕ) : 0 < Fintype.card (Prefix h k) := by
  rw [prefix_card]
  exact Nat.pow_pos (Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))

theorem catalog_time_le_layer {W V offset cut n : ℕ} (hfit : offset+V ≤ W)
    (hhalf : cut ≤ V/2) (hn : 0 < n) :
    LightReportingSuffixCatalogSetup.time W V cut offset n ≤
      100000*(W+1)^5*n*V.choose cut := by
  have hcut : cut ≤ V := hhalf.trans (Nat.div_le_self _ _)
  have ht := LightReportingSuffixCatalogSetup.time_bound (n := n) hfit hcut
  have hc := downsetCap_add_one_le_layer hhalf
  have hv : V+2 ≤ 2*(W+1) := by omega
  have hn' : n+1 ≤ 2*n := by omega
  calc
    _ ≤ 23000*(W+1)^4*((V+2)*V.choose cut)*(n+1) :=
      ht.trans (Nat.mul_le_mul_right (n+1) (Nat.mul_le_mul_left (23000*(W+1)^4) hc))
    _ ≤ 23000*(W+1)^4*((2*(W+1))*V.choose cut)*(2*n) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left (23000*(W+1)^4) (Nat.mul_le_mul_right _ hv)) hn'
    _ = 92000*(W+1)^5*n*V.choose cut := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide)))

theorem block_catalog_time_le_layer {h J k cut : ℕ} (hk : k ≤ J)
    (hcut : cut ≤ residualSize h J k) :
    LightReportingSuffixCatalogSetup.time (width h J) (suffixStage J (512*h) k) cut (k*(512*h))
      (Fintype.card (Prefix h k)) ≤
      100000*(width h J+1)^5*(((512*h).choose (2*h)*(2*h).choose h)^k)*
        (256*residualSize h J k).choose cut := by
  have hhalf : cut ≤ suffixStage J (512*h) k/2 := by
    rw [suffix_width_eq]
    omega
  calc
    _ ≤ 100000*(width h J+1)^5*(Fintype.card (Prefix h k))*
        (suffixStage J (512*h) k).choose cut :=
      catalog_time_le_layer (W := width h J) (V := suffixStage J (512*h) k)
        (offset := k*(512*h)) (ReportingHostSuffix.block_fit hk) hhalf (prefix_card_pos h k)
    _ = _ := by rw [prefix_card,suffix_width_eq]

theorem prefix_card_eq_ledger {n h k : ℕ} (hsize : 2*h = Scales.muZero n) :
    Fintype.card (Prefix h k) = CostLedger.prefixChoices n k := by
  have hhalf : Scales.muZero n/2 = h := by omega
  have hwidth : 512*h = 256*Scales.muZero n := by omega
  rw [prefix_card,CostLedger.prefixChoices,CostLedger.microOutputs,CostLedger.microPartitions,
    hwidth,hsize,hhalf]

theorem catalog_time_le_prefixBoxes {n h J k : ℕ}
    (hsize : 2*h = Scales.muZero n) (hblocks : J = Scales.blockCount (Scales.inputBits n))
    (hk : k ≤ J) :
    LightReportingSuffixCatalogSetup.time (width h J) (suffixStage J (512*h) k)
      (Switch.residualSize n k-Switch.actualSwitch n k) (k*(512*h))
      (Fintype.card (Prefix h k)) ≤ 100000*(width h J+1)^5*CostLedger.prefixBoxes n k := by
  have hres : residualSize h J k = Switch.residualSize n k := by
    simp only [residualSize,Switch.residualSize,hsize,hblocks]
  have hcount : (((512*h).choose (2*h)*(2*h).choose h)^k) = CostLedger.prefixChoices n k :=
    (prefix_card h k).symm.trans (prefix_card_eq_ledger hsize)
  have hcut : Switch.residualSize n k-Switch.actualSwitch n k ≤ residualSize h J k := by
    rw [hres]
    exact Nat.sub_le _ _
  have ht := block_catalog_time_le_layer hk hcut
  calc
    _ ≤ 100000*(width h J+1)^5*(((512*h).choose (2*h)*(2*h).choose h)^k)*
        (256*residualSize h J k).choose (Switch.residualSize n k-Switch.actualSwitch n k) := ht
    _ = _ := by rw [hcount,hres]; simp only [CostLedger.prefixBoxes,CostLedger.suffixBoxes,Nat.mul_assoc]

theorem actual_catalog_time_le_prefixBoxes {n k : ℕ}
    (hk : k ≤ Scales.blockCount (Scales.inputBits n)) :
    LightReportingSuffixCatalogSetup.time
      (width (Scales.microHalf (Scales.inputBits n)) (Scales.blockCount (Scales.inputBits n)))
      (suffixStage (Scales.blockCount (Scales.inputBits n))
        (512*Scales.microHalf (Scales.inputBits n)) k)
      (Switch.residualSize n k-Switch.actualSwitch n k)
      (k*(512*Scales.microHalf (Scales.inputBits n)))
      (Fintype.card (Prefix (Scales.microHalf (Scales.inputBits n)) k)) ≤
      100000*(width (Scales.microHalf (Scales.inputBits n)) (Scales.blockCount (Scales.inputBits n))+1)^5*
        CostLedger.prefixBoxes n k :=
  catalog_time_le_prefixBoxes rfl rfl hk

end ThreeSum.ReportingHostCatalogCosts

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
























theorem sort_clog_le {W n : ℕ} (hn : n ≤ 2^(2*W)) : Nat.clog 2 n ≤ 2*W :=
  Nat.clog_le_of_le_pow hn







theorem index_setup_time_le {W n : ℕ} (hn : n ≤ 2^(2*W)) :
    LightReportingSortedCatalog.time W n ≤ 1000*(W+1)*(n+1) := by
  have ht := LightReportingSortedCatalog.time_bound W n
  have hc := sort_clog_le hn
  have hm := Nat.mul_le_mul_left (200*(n+1)) (Nat.add_le_add_right hc 1)
  nlinarith






theorem prefix_index_setup_time_le {h J k : ℕ} (hk : k ≤ J) :
    LightReportingSortedCatalog.time (J*(512*h)) (LightReportingPrefixCatalog.count h k) ≤
      1000*(J*(512*h)+1)*(LightReportingPrefixCatalog.count h k+1) :=
  index_setup_time_le (ReportingHostPackedCatalog.prefix_count_le_pow hk)

end ThreeSum.ReportingHostCatalogIndexCosts

end

section


/-!
# Charge the complete shared reporting catalog constructor

The actual prefix constructor enumerates the local balanced pairs even at
level zero. That additive local cost is included explicitly and bounded by
the existing local-search factor. Prefix generation, suffix tables and the
sorted physical lookup index are all charged in the complete bound below.
-/

namespace ThreeSum.SharedReportingCosts

open Scales CostLedger ReportingHostPrefixCatalog

set_option maxHeartbeats 1700000
set_option maxRecDepth 10000














/-- The complete local row-pair enumeration is a subpolynomial microblock
factor, including at level zero where the prefix count itself is one. -/
theorem local_count_le_search (n : ℕ) : localCount n ≤ localSearch 257 n := by
  have hsize : 2*half n=muZero n := rfl
  unfold localCount LightReportingPrefixArrays.localCount localWidth
  calc
    _ ≤ 2^(512*half n)*2^(2*half n) :=
      Nat.mul_le_mul (Nat.choose_le_two_pow _ _) (Nat.choose_le_two_pow _ _)
    _ = 2^(257*(2*half n)) := by rw [← pow_add]; congr 1; ring
    _ = 2^(257*muZero n) := by rw [hsize]
    _ ≤ localSearch 257 n :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 257 (Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) _))

theorem prefix_count_eq (n k : ℕ) :
    LightReportingPrefixCatalog.count (half n) k=prefixChoices n k := by
  have hcard : LightReportingPrefixCatalog.count (half n) k=Fintype.card (Prefix (half n) k) := by
    rw [prefix_card]
    rfl
  exact hcard.trans (ReportingHostCatalogCosts.prefix_card_eq_ledger rfl)

theorem prefix_count_le_boxes (n k : ℕ) :
    LightReportingPrefixCatalog.count (half n) k ≤ prefixBoxes n k := by
  rw [prefix_count_eq]
  exact Nat.le_mul_of_pos_right _ (suffixBoxes_pos n k)

/-- Every operation in the closed52-procedure constructor is included. -/
theorem time_le_boxes_sourceProof {n k : ℕ} (hk : k ≤ blocks n) :
    time n k ≤ overhead n*prefixBoxes n k := by
  let N := LightReportingPrefixCatalog.count (half n) k
  let X := prefixBoxes n k
  have hX : 0 < X := prefixBoxes_pos n k
  have hN : N ≤ X := prefix_count_le_boxes n k
  have hN1 : N+1 ≤ 2*X := by omega
  have hlocal := LightReportingPrefixArrays.time_bound (L := localWidth n) (h := half n) (k := k)
    (by unfold localWidth; omega)
  have hE := local_count_le_search n
  have hlocalTerm := Nat.mul_le_mul_left (5000*(localWidth n+1)^2) (Nat.add_le_add_right hE 1)
  have hlocalTermX := (Nat.le_mul_of_pos_right
    (5000*(localWidth n+1)^2*(localSearch 257 n+1)) hX)
  have hprefixTerm := Nat.mul_le_mul (Nat.mul_le_mul_left 600 (Nat.add_le_add_right hk 1)) hN1
  have hprefixTime : LightReportingPrefixArrays.time (localWidth n) (half n) k ≤
      (5000*(localWidth n+1)^2*(localSearch 257 n+1))*X+1200*(blocks n+1)*X+300 := by
    change LightReportingPrefixArrays.time (localWidth n) (half n) k ≤
      5000*(localWidth n+1)^2*(localCount n+1)+600*(k+1)*(N+1)+300 at hlocal
    have hprefixTerm' : 600*(k+1)*(N+1) ≤ 1200*(blocks n+1)*X := by
      convert hprefixTerm using 1 <;> ring
    omega
  have hsuffix := ReportingHostCatalogCosts.actual_catalog_time_le_prefixBoxes hk
  have hcard : Fintype.card (Prefix (half n) k)=N := by rw [prefix_card]; rfl
  change LightReportingSuffixCatalogSetup.time (width n) ((blocks n-k)*localWidth n)
    (Switch.residualSize n k-Switch.actualSwitch n k) (k*localWidth n)
    (Fintype.card (Prefix (half n) k)) ≤ 100000*(width n+1)^5*X at hsuffix
  rw [hcard] at hsuffix
  change LightReportingSuffixCatalogSetup.time (width n) ((blocks n-k)*localWidth n)
    (Switch.residualSize n k-Switch.actualSwitch n k) (k*localWidth n) N ≤
    100000*(width n+1)^5*X at hsuffix
  have hsort := ReportingHostCatalogIndexCosts.prefix_index_setup_time_le
    (h := half n) (J := blocks n) hk
  change LightReportingSortedCatalog.time (width n) N ≤ 1000*(width n+1)*(N+1) at hsort
  have hsortX : LightReportingSortedCatalog.time (width n) N ≤ 2000*(width n+1)*X := by
    calc
      _ ≤ 1000*(width n+1)*(N+1) := hsort
      _ ≤ 1000*(width n+1)*(2*X) := Nat.mul_le_mul_left _ hN1
      _ = _ := by ring
  have hconstant : 1050 ≤ 1050*X := Nat.le_mul_of_pos_right _ hX
  unfold time LightReportingCatalogIndex.time LightReportingPrefixCatalog.time
  change LightReportingPrefixArrays.time (localWidth n) (half n) k+
    LightReportingSuffixCatalogSetup.time (width n) ((blocks n-k)*localWidth n)
      (Switch.residualSize n k-Switch.actualSwitch n k) (k*localWidth n) N+500+
    LightReportingSortedCatalog.time (width n) N+250 ≤ overhead n*X
  unfold overhead
  simp only [Nat.add_mul]
  omega




























end ThreeSum.SharedReportingCosts

end


theorem solution : ∀ {n k : Nat},
  @LE.le.{0} Nat instLENat k (ThreeSum.SharedReportingCosts.blocks n) →
    @LE.le.{0} Nat instLENat (ThreeSum.SharedReportingCosts.time n k)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.SharedReportingCosts.overhead n)
        (ThreeSum.CostLedger.prefixBoxes n k)) := by
  exact @ThreeSum.SharedReportingCosts.time_le_boxes_sourceProof

#print axioms solution
