-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.time_le_boxes
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:26:55.656526+00:00
-- url     : https://prove2.me/submissions/db455a61-b4a6-4718-b75d-0b24729fd301

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
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SharedReportingCosts_local_count_le_search
import Theorems.Thm_ThreeSum_LayerCounts_edgeSet_card
import Theorems.Thm_ThreeSum_LightRadixKeys_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixCatalogSetup_time_bound
import Theorems.Thm_ThreeSum_SubsetAddress_enumerationWork_bound

namespace Filter
end Filter
namespace Finset
end Finset
namespace Light
end Light
namespace Real
end Real
namespace Set
end Set
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
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.LayerCounts
end ThreeSum.LayerCounts
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightQueryEnumeration
end ThreeSum.LightQueryEnumeration
namespace ThreeSum.LightQueryWeights
end ThreeSum.LightQueryWeights
namespace ThreeSum.LightReportingPairRows
end ThreeSum.LightReportingPairRows
namespace ThreeSum.LightReportingPrefixArrays
end ThreeSum.LightReportingPrefixArrays
namespace ThreeSum.LightReportingSortedCatalog
end ThreeSum.LightReportingSortedCatalog
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightSubsetEnumeration
end ThreeSum.LightSubsetEnumeration
namespace ThreeSum.LightSubsetEnumerationSetup
end ThreeSum.LightSubsetEnumerationSetup
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.ReportingHostCatalogCosts
end ThreeSum.ReportingHostCatalogCosts
namespace ThreeSum.ReportingHostCatalogIndexCosts
end ThreeSum.ReportingHostCatalogIndexCosts
namespace ThreeSum.ReportingHostPackedCatalog
end ThreeSum.ReportingHostPackedCatalog
namespace ThreeSum.ReportingHostPairEnumeration
end ThreeSum.ReportingHostPairEnumeration
namespace ThreeSum.ReportingHostPairSegments
end ThreeSum.ReportingHostPairSegments
namespace ThreeSum.ReportingHostPrefixCatalog
end ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.ReportingHostSuffixCosts
end ThreeSum.ReportingHostSuffixCosts
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingCosts
end ThreeSum.SharedReportingCosts
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
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LayerCounts
end ThreeSum1960614.Machine.ThreeSum.LayerCounts
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightQueryWeights
end ThreeSum1960614.Machine.ThreeSum.LightQueryWeights
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows
end ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSortedCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSortedCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup
end ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.MaskErase
end ThreeSum1960614.Machine.ThreeSum.MaskErase
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
end ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogCosts
end ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogCosts
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogIndexCosts
end ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogIndexCosts
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixCosts
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixCosts
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts
end ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.Switch
end ThreeSum1960614.Machine.ThreeSum.Switch

namespace ThreeSum1960614.Machine

/-!
# Exact counts for the local subset graph

These are counts of the executable finite sets used by the graph, rather
than abstract numerical cardinality hypotheses.  An edge is an ordered
pair of disjoint `h`-subsets of `Fin L`.
-/

namespace ThreeSum.LayerCounts
open _root_.ThreeSum.LayerCounts


open _root_.Finset

















theorem vertex_degree_identity (L h : ℕ) :
    L.choose h * (L - h).choose h = L.choose (2 * h) * (2 * h).choose h := by
  simpa [show 2 * h - h = h by omega] using
    (Nat.choose_mul (n := L) (k := 2 * h) (s := h) (by omega)).symm



end ThreeSum.LayerCounts

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
# A fixed subset-layer enumerator with its own power-table construction

The main theorem has no supplied lookup-table correctness assumption. The
only auxiliary memory is a table of `L+1` powers of two, built once before
the recursive enumeration. The output has exactly `L.choose k` cells.
-/

namespace ThreeSum.LightSubsetEnumerationSetup
open _root_.ThreeSum.LightSubsetEnumerationSetup


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}











theorem time_bound (L k : ℕ) : _root_.ThreeSum.LightSubsetEnumerationSetup.time L k ≤ 800*(L+1)*(L.choose k+1) := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.time_bound L k
  unfold _root_.ThreeSum.LightSubsetEnumerationSetup.time _root_.Light.powTableTime
  nlinarith

end ThreeSum.LightSubsetEnumerationSetup

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The concrete local subset graph and its binary words

A left vertex has ones exactly on its `h`-subset.  A right vertex has zeros
exactly on its `h`-subset.  The endpoint maps, their separation, and the
equality mask are proved directly from finite-set membership.
-/

namespace ThreeSum.LocalGraph
open _root_.ThreeSum.LocalGraph


variable {α : Type*} [DecidableEq α]

















section ConcreteGraph

open _root_.ThreeSum.LayerCounts
open _root_.ThreeSum1960614.Machine.ThreeSum.LayerCounts



variable {L h : ℕ}





































theorem edge_card (L h : ℕ) :
    Fintype.card (_root_.ThreeSum.LocalGraph.Edge L h) = L.choose (2 * h) * (2 * h).choose h := by
  rw [Fintype.card_coe, _root_.ThreeSum.LayerCounts.edgeSet_card]











end ConcreteGraph

end ThreeSum.LocalGraph

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual finite hierarchy counts

These are the binomial counts used by the concrete microblock hierarchy.
Every prefix partition is included.  The integer switch and its rounding
allowance are applied before any asymptotic estimate is made.  The counts
in this module are combinatorial work counts; the implementation's operation
counts, raw wanted incidences, and false-mass bounds are separate interfaces.
-/

namespace ThreeSum.CostLedger
open _root_.ThreeSum.CostLedger


open _root_.Filter
open _root_.Set
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Switch
open scoped _root_.Topology
open scoped _root_.BigOperators

set_option maxHeartbeats 400000





















theorem microOutputs_pos (n : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.microOutputs n :=
  Nat.choose_pos (by omega)

theorem microPartitions_pos (n : ℕ) : 0 < _root_.ThreeSum.CostLedger.microPartitions n :=
  Nat.choose_pos (Nat.div_le_self _ _)

theorem prefixChoices_pos (n j : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixChoices n j :=
  Nat.pow_pos (Nat.mul_pos (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.microOutputs_pos n) (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.microPartitions_pos n))

theorem suffixBoxes_pos (n j : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.suffixBoxes n j :=
  Nat.choose_pos (by omega)

theorem prefixBoxes_pos (n j : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixBoxes n j :=
  Nat.mul_pos (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixChoices_pos n j) (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.suffixBoxes_pos n j)

noncomputable section















end
end ThreeSum.CostLedger

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
# Exact prefix catalog keys and sharing for fixed source occurrences

A catalog key consists only of the first k ordered disjoint balanced row
pairs. Its exact cardinality is (microOutputs*microPartitions)^k. Neither the
remaining output rows nor the wanted A-index enter a local box table once
the global occurrence vector is fixed.
-/

namespace ThreeSum.ReportingHostPrefixCatalog
open _root_.ThreeSum.ReportingHostPrefixCatalog


open _root_.Finset
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LayerCounts
open _root_.ThreeSum1960614.Machine.ThreeSum.LayerCounts
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix

set_option linter.unusedSectionVars false



theorem prefix_card (h k : ℕ) :
    Fintype.card (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k) = ((464*h).choose (2*h)*(2*h).choose h)^k := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix,Fintype.card_fun,Fintype.card_fin,_root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph.edge_card]



















section Sources

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]



















end Sources

end ThreeSum.ReportingHostPrefixCatalog

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





theorem suffix_width_eq (h J k : ℕ) :
    _root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k = 232*_root_.ThreeSum.LightBlockQuery.residualSize h J k := by
  unfold _root_.ThreeSum.BlockIndexedQuery.suffixStage _root_.ThreeSum.LightBlockQuery.residualSize
  ring



end ThreeSum.ReportingHostSuffixCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual direct construction of all local balanced row pairs

An own-power layer enumerator constructs the left subsets. For each left
subset, an actual output-sensitive query enumerator constructs its disjoint
right subsets, and an affine pass writes the matching repeated left mask.
-/

namespace ThreeSum.LightReportingPairRows
open _root_.ThreeSum.LightReportingPairRows


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostPairEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration

set_option maxHeartbeats 1800000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}















theorem time_bound {L h : ℕ} (hh : 2*h ≤ L) :
    _root_.ThreeSum.LightReportingPairRows.time L h ≤ 4000*(L+1)^2*(L.choose (2*h)*(2*h).choose h+1) := by
  have hdeg : 0 < (L-h).choose h := Nat.choose_pos (by omega)
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup.time_bound L h
  have hq := _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration.time_bound (t := h) (Nat.sub_le L h)
  have hlinear : L+1 ≤ (L+1)^2 := by nlinarith
  have hv : L.choose h ≤ L.choose h*(L-h).choose h := Nat.le_mul_of_pos_right _ hdeg
  have hm := Nat.mul_le_mul_left (L.choose h) hq
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.LayerCounts.vertex_degree_identity]
  unfold _root_.ThreeSum.LightReportingPairRows.time _root_.ThreeSum.LightReportingPairRows.roundTime _root_.ThreeSum.LightReportingAffine.time
  nlinarith

end ThreeSum.LightReportingPairRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Charging the actual shared suffix catalog to the original finite ledger

The bound uses the exact physically constructed local table size and the
proved full prefix-key cardinality. Physical enumeration and lookup of those
prefix keys remain separate executable components.
-/

namespace ThreeSum.ReportingHostCatalogCosts
open _root_.ThreeSum.ReportingHostCatalogCosts


set_option maxRecDepth 8000

open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixCosts

theorem prefix_card_pos (h k : ℕ) : 0 < Fintype.card (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.prefix_card]
  exact Nat.pow_pos (Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))

theorem catalog_time_le_layer {W V offset cut n : ℕ} (hfit : offset+V ≤ W)
    (hhalf : cut ≤ V/2) (hn : 0 < n) :
    _root_.ThreeSum.LightReportingSuffixCatalogSetup.time W V cut offset n ≤
      100000*(W+1)^5*n*V.choose cut := by
  have hcut : cut ≤ V := hhalf.trans (Nat.div_le_self _ _)
  have ht := _root_.ThreeSum.LightReportingSuffixCatalogSetup.time_bound (n := n) hfit hcut
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixCosts.downsetCap_add_one_le_layer hhalf
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
    (hcut : cut ≤ _root_.ThreeSum.LightBlockQuery.residualSize h J k) :
    _root_.ThreeSum.LightReportingSuffixCatalogSetup.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) cut (k*(464*h))
      (Fintype.card (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k)) ≤
      100000*(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)^5*(((464*h).choose (2*h)*(2*h).choose h)^k)*
        (232*_root_.ThreeSum.LightBlockQuery.residualSize h J k).choose cut := by
  have hhalf : cut ≤ _root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k/2 := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixCosts.suffix_width_eq]
    omega
  calc
    _ ≤ 100000*(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)^5*(Fintype.card (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k))*
        (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k).choose cut :=
      _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogCosts.catalog_time_le_layer (W := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (V := _root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k)
        (offset := k*(464*h)) (_root_.ThreeSum.ReportingHostSuffix.block_fit hk) hhalf (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogCosts.prefix_card_pos h k)
    _ = _ := by rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.prefix_card,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixCosts.suffix_width_eq]

theorem prefix_card_eq_ledger {n h k : ℕ} (hsize : 2*h = _root_.ThreeSum.Scales.muZero n) :
    Fintype.card (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k) = _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixChoices n k := by
  have hhalf : _root_.ThreeSum.Scales.muZero n/2 = h := by omega
  have hwidth : 464*h = 232*_root_.ThreeSum.Scales.muZero n := by omega
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.prefix_card,_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixChoices,_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.microOutputs,_root_.ThreeSum.CostLedger.microPartitions,
    hwidth,hsize,hhalf]

theorem catalog_time_le_prefixBoxes {n h J k : ℕ}
    (hsize : 2*h = _root_.ThreeSum.Scales.muZero n) (hblocks : J = _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))
    (hk : k ≤ J) :
    _root_.ThreeSum.LightReportingSuffixCatalogSetup.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k)
      (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n k-_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n k) (k*(464*h))
      (Fintype.card (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix h k)) ≤ 100000*(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)^5*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixBoxes n k := by
  have hres : _root_.ThreeSum.LightBlockQuery.residualSize h J k = _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n k := by
    simp only [_root_.ThreeSum.LightBlockQuery.residualSize,_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize,hsize,hblocks]
  have hcount : (((464*h).choose (2*h)*(2*h).choose h)^k) = _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixChoices n k :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.prefix_card h k).symm.trans (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogCosts.prefix_card_eq_ledger hsize)
  have hcut : _root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n k-_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n k ≤ _root_.ThreeSum.LightBlockQuery.residualSize h J k := by
    rw [hres]
    exact Nat.sub_le _ _
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogCosts.block_catalog_time_le_layer hk hcut
  calc
    _ ≤ 100000*(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)^5*(((464*h).choose (2*h)*(2*h).choose h)^k)*
        (232*_root_.ThreeSum.LightBlockQuery.residualSize h J k).choose (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n k-_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n k) := ht
    _ = _ := by rw [hcount,hres]; simp only [_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixBoxes,_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.suffixBoxes,Nat.mul_assoc]

theorem actual_catalog_time_le_prefixBoxes {n k : ℕ}
    (hk : k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) :
    _root_.ThreeSum.LightReportingSuffixCatalogSetup.time
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)))
      (_root_.ThreeSum.BlockIndexedQuery.suffixStage (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))
        (464*_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) k)
      (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n k-_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n k)
      (k*(464*_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)))
      (Fintype.card (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) k)) ≤
      100000*(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))+1)^5*
        _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixBoxes n k :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogCosts.catalog_time_le_prefixBoxes rfl rfl hk

end ThreeSum.ReportingHostCatalogCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing both complete prefix-mask product arrays in the same record order

The local pair arrays are built directly, then the verified positional-key
host is used twice with radix 2^L. Both results share the literal tuple order,
including separate entries for pairs with equal left or right projections.
-/

namespace ThreeSum.LightReportingPrefixArrays
open _root_.ThreeSum.LightReportingPrefixArrays


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostPairEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration
open _root_.ThreeSum.ReportingHostPairSegments
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairSegments

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}











theorem time_bound {L h k : ℕ} (hh : 2*h ≤ L) :
    _root_.ThreeSum.LightReportingPrefixArrays.time L h k ≤ 5000*(L+1)^2*(_root_.ThreeSum.LightReportingPrefixArrays.localCount L h+1)+
      600*(k+1)*((_root_.ThreeSum.LightReportingPrefixArrays.localCount L h)^k+1)+300 := by
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows.time_bound hh
  have hk := _root_.ThreeSum.LightRadixKeys.time_bound (_root_.ThreeSum.LightReportingPrefixArrays.localCount L h) k
    (Nat.one_le_of_lt (Nat.mul_pos (Nat.choose_pos hh) (Nat.choose_pos (by omega))))
  unfold _root_.ThreeSum.LightReportingPrefixArrays.time _root_.Light.powTableTime
  change _root_.ThreeSum.LightReportingPairRows.time L h ≤ 4000*(L+1)^2*(_root_.ThreeSum.LightReportingPrefixArrays.localCount L h+1) at hp
  nlinarith

end ThreeSum.LightReportingPrefixArrays

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
# Actual packed-key construction and sorted catalog index

The powers table supplies the physical mask radix. A linear pass retains the
original catalog index as a low digit, and the benchmark's verified merge
sort orders these records without changing their multiplicity or payload.
-/

namespace ThreeSum.LightReportingSortedCatalog
open _root_.ThreeSum.LightReportingSortedCatalog


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostPackedCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}













theorem time_bound (W n : ℕ) : _root_.ThreeSum.LightReportingSortedCatalog.time W n ≤ 200*(W+1)+200*(n+1)*(Nat.clog 2 n+1) := by
  unfold _root_.ThreeSum.LightReportingSortedCatalog.time _root_.Light.powTableTime _root_.ThreeSum.LightReportingPackKeys.time _root_.Light.sortTime
  have hh : n-1 ≤ n := Nat.sub_le _ _
  nlinarith

end ThreeSum.LightReportingSortedCatalog

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



theorem index_setup_time_le {W n : ℕ} (hn : n ≤ 2^(2*W)) :
    _root_.ThreeSum.LightReportingSortedCatalog.time W n ≤ 1000*(W+1)*(n+1) := by
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSortedCatalog.time_bound W n
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogIndexCosts.sort_clog_le hn
  have hm := Nat.mul_le_mul_left (200*(n+1)) (Nat.add_le_add_right hc 1)
  nlinarith



theorem prefix_index_setup_time_le {h J k : ℕ} (hk : k ≤ J) :
    _root_.ThreeSum.LightReportingSortedCatalog.time (J*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k) ≤
      1000*(J*(464*h)+1)*(_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k+1) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogIndexCosts.index_setup_time_le (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.prefix_count_le_pow hk)

end ThreeSum.ReportingHostCatalogIndexCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Charge the complete shared reporting catalog constructor

The actual prefix constructor enumerates the local balanced pairs even at
level zero. That additive local cost is included explicitly and bounded by
the existing local-search factor. Prefix generation, suffix tables and the
sorted physical lookup index are all charged in the complete bound below.
-/

namespace ThreeSum.SharedReportingCosts
open _root_.ThreeSum.SharedReportingCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog

set_option maxHeartbeats 1700000
set_option maxRecDepth 10000













theorem prefix_count_eq (n k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count (_root_.ThreeSum.SharedReportingCosts.half n) k=_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixChoices n k := by
  have hcard : _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count (_root_.ThreeSum.SharedReportingCosts.half n) k=Fintype.card (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix (_root_.ThreeSum.SharedReportingCosts.half n) k) := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.prefix_card]
    rfl
  exact hcard.trans (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogCosts.prefix_card_eq_ledger rfl)

theorem prefix_count_le_boxes (n k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count (_root_.ThreeSum.SharedReportingCosts.half n) k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixBoxes n k := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.prefix_count_eq]
  exact Nat.le_mul_of_pos_right _ (_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.suffixBoxes_pos n k)















end ThreeSum.SharedReportingCosts

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.SharedReportingCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts

open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
set_option maxHeartbeats 1700000
set_option maxRecDepth 10000
section

/-- Every operation in the closed52-procedure constructor is included. -/
theorem ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.time_le_boxes__implementation_511a5ff46e {n k : ℕ} (hk : k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.time n k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.overhead n*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixBoxes n k := by
  let N := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count (_root_.ThreeSum.SharedReportingCosts.half n) k
  let X := _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixBoxes n k
  have hX : 0 < X := _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.prefixBoxes_pos n k
  have hN : N ≤ X := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.prefix_count_le_boxes n k
  have hN1 : N+1 ≤ 2*X := by omega
  have hlocal := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixArrays.time_bound (L := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.localWidth n) (h := _root_.ThreeSum.SharedReportingCosts.half n) (k := k)
    (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.localWidth; omega)
  have hE := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.local_count_le_search n
  have hlocalTerm := Nat.mul_le_mul_left (5000*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.localWidth n+1)^2) (Nat.add_le_add_right hE 1)
  have hlocalTermX := (Nat.le_mul_of_pos_right
    (5000*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.localWidth n+1)^2*(_root_.ThreeSum.Scales.localSearch 257 n+1)) hX)
  have hprefixTerm := Nat.mul_le_mul (Nat.mul_le_mul_left 600 (Nat.add_le_add_right hk 1)) hN1
  have hprefixTime : _root_.ThreeSum.LightReportingPrefixArrays.time (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.localWidth n) (_root_.ThreeSum.SharedReportingCosts.half n) k ≤
      (5000*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.localWidth n+1)^2*(_root_.ThreeSum.Scales.localSearch 257 n+1))*X+1200*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n+1)*X+300 := by
    change _root_.ThreeSum.LightReportingPrefixArrays.time (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.localWidth n) (_root_.ThreeSum.SharedReportingCosts.half n) k ≤
      5000*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.localWidth n+1)^2*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.localCount n+1)+600*(k+1)*(N+1)+300 at hlocal
    have hprefixTerm' : 600*(k+1)*(N+1) ≤ 1200*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n+1)*X := by
      convert hprefixTerm using 1 <;> ring
    omega
  have hsuffix := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogCosts.actual_catalog_time_le_prefixBoxes hk
  have hcard : Fintype.card (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix (_root_.ThreeSum.SharedReportingCosts.half n) k)=N := by rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.prefix_card]; rfl
  change _root_.ThreeSum.LightReportingSuffixCatalogSetup.time (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.width n) ((_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n-k)*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.localWidth n)
    (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n k-_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n k) (k*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.localWidth n)
    (Fintype.card (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog.Prefix (_root_.ThreeSum.SharedReportingCosts.half n) k)) ≤ 100000*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.width n+1)^5*X at hsuffix
  rw [hcard] at hsuffix
  change _root_.ThreeSum.LightReportingSuffixCatalogSetup.time (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.width n) ((_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n-k)*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.localWidth n)
    (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n k-_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n k) (k*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.localWidth n) N ≤
    100000*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.width n+1)^5*X at hsuffix
  have hsort := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostCatalogIndexCosts.prefix_index_setup_time_le
    (h := _root_.ThreeSum.SharedReportingCosts.half n) (J := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n) hk
  change _root_.ThreeSum.LightReportingSortedCatalog.time (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.width n) N ≤ 1000*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.width n+1)*(N+1) at hsort
  have hsortX : _root_.ThreeSum.LightReportingSortedCatalog.time (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.width n) N ≤ 2000*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.width n+1)*X := by
    calc
      _ ≤ 1000*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.width n+1)*(N+1) := hsort
      _ ≤ 1000*(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.width n+1)*(2*X) := Nat.mul_le_mul_left _ hN1
      _ = _ := by ring
  have hconstant : 1050 ≤ 1050*X := Nat.le_mul_of_pos_right _ hX
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.time _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogIndex.time _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.time
  change _root_.ThreeSum.LightReportingPrefixArrays.time (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.localWidth n) (_root_.ThreeSum.SharedReportingCosts.half n) k+
    _root_.ThreeSum.LightReportingSuffixCatalogSetup.time (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.width n) ((_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.blocks n-k)*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.localWidth n)
      (_root_.ThreeSum1960614.Machine.ThreeSum.Switch.residualSize n k-_root_.ThreeSum1960614.Machine.ThreeSum.Switch.actualSwitch n k) (k*_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.localWidth n) N+500+
    _root_.ThreeSum.LightReportingSortedCatalog.time (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.width n) N+250 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.overhead n*X
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.overhead
  simp only [Nat.add_mul]
  omega
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.time_le_boxes__implementation_511a5ff46e) := (@ThreeSum1960614.Machine.ThreeSum.SharedReportingCosts.time_le_boxes__implementation_511a5ff46e)

#print axioms solution
