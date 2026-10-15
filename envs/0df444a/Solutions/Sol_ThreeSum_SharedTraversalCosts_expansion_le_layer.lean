-- Prove2me | solution 1 for ThreeSum.SharedTraversalCosts.expansion_le_layer
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:07:08.209139+00:00
-- url     : https://prove2.me/submissions/95ce6579-75ca-4922-827b-94f7c7c36c9e

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle12
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
import Theorems.Thm_ThreeSum_LightReportingCatalogExpand_time_bound


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
namespace ThreeSum.LightReportingPositiveMasks
end ThreeSum.LightReportingPositiveMasks
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostPositive
end ThreeSum.ReportingHostPositive
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-! # Actual aligned gathering of both selected reporting-prefix mask arrays -/

namespace ThreeSum.LightReportingGatherPair

open Light

variable {lim : Limits}









































theorem time_bound (t : ℕ) : time t ≤ 80*t+80 := by
  unfold time LightReportingGather.time
  omega

end ThreeSum.LightReportingGatherPair

end

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
# Actual parent expansion returning compact positive-prefix mask arrays

All child construction, physical catalog lookup, exact querying, positive
selection, and aligned mask gathering are executed by this closed program.
Only the actual positive output intervals may change below child scratch.
-/

namespace ThreeSum.LightReportingPositiveExpand

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockIndex BlockMaskLayout BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
open ReportingHostMasks LightBlockChildrenIndexed ReportingHostPositive LightReportingPositiveMasks

set_option maxHeartbeats 2200000
set_option maxRecDepth 8000

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
















































































































theorem time_bound {h J k t : ℕ} (hk : k < J) (ht : t ≤ residualSize h J (k+1)+1) :
    time h J k t ≤
      26000*(width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J (k+1)) t+1)*(groupSize h+1) := by
  have he := LightReportingCatalogExpand.time_bound hk ht
  have hg := LightReportingGatherPair.time_bound (groupSize h)
  have hp : 1 ≤ (width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J (k+1)) t+1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hm := Nat.mul_le_mul_right (groupSize h+1) hp
  unfold time
  nlinarith

end ThreeSum.LightReportingPositiveExpand

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

theorem expansion_le_layer_sourceProof {h J k t : ℕ} (hk : k < J)
    (ht : t ≤ residualSize h J (k+1)/2) :
    LightReportingPositiveExpand.time h J k t+200 ≤
      overhead h J*groupSize h*(residualSize h J (k+1)).choose t := by
  let B := size h J
  let Q := (residualSize h J (k+1)).choose t
  have hb := size_bounds h J
  have hB : 1 ≤ B^4 := Nat.one_le_pow _ _ hb.1
  have hq : 1 ≤ Q := Nat.choose_pos (ht.trans (Nat.div_le_self _ _))
  have hg : 1 ≤ groupSize h := Nat.choose_pos (by omega)
  have hqitems := query_items_le_layer ht
  have hqB := hqitems.trans (Nat.mul_le_mul_right Q (residual_le_size h J (k+1)))
  have he := LightReportingPositiveExpand.time_bound hk (by omega : t ≤ residualSize h J (k+1)+1)
  have he' : LightReportingPositiveExpand.time h J k t ≤ 104000*B^4*groupSize h*Q := by
    calc
      _ ≤ 26000*B^3*(2*B*Q)*(2*groupSize h) := he.trans
        (Nat.mul_le_mul (Nat.mul_le_mul
          (Nat.mul_le_mul_left 26000 (Nat.pow_le_pow_left hb.2.2.2.1 3)) hqB) (by omega))
      _ = _ := by ring
  have h1 := Nat.mul_le_mul (Nat.mul_le_mul hB hg) hq
  unfold overhead
  change _ ≤ 200000*B^4*groupSize h*Q
  nlinarith





























end ThreeSum.SharedTraversalCosts

end


theorem solution : ∀ {h J k t : Nat},
  @LT.lt.{0} Nat instLTNat k J →
    @LE.le.{0} Nat instLENat t
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
          (ThreeSum.LightBlockQuery.residualSize h J
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
      @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (ThreeSum.LightReportingPositiveExpand.time h J k t)
          (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.SharedTraversalCosts.overhead h J)
            (ThreeSum.LocalCoverBounds.groupSize h))
          ((ThreeSum.LightBlockQuery.residualSize h J
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))).choose
            t)) := by
  exact @ThreeSum.SharedTraversalCosts.expansion_le_layer_sourceProof

#print axioms solution
