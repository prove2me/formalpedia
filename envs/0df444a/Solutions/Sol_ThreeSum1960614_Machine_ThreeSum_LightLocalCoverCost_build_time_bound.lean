-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCost.build_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:15:36.803679+00:00
-- url     : https://prove2.me/submissions/99e05620-a27c-40ae-9d53-de01b24fae5c

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
import Mathlib.Data.List.Range
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
import Theorems.Thm_ThreeSum_SubsetAddress_enumerationWork_bound

local instance platformRadixNonzero_80b2377fda (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightLocalCoverCost
end ThreeSum.LightLocalCoverCost
namespace ThreeSum.LightLocalCoverRow
end ThreeSum.LightLocalCoverRow
namespace ThreeSum.LightMaskBits
end ThreeSum.LightMaskBits
namespace ThreeSum.LightPairFlags
end ThreeSum.LightPairFlags
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightSubsetEnumeration
end ThreeSum.LightSubsetEnumeration
namespace ThreeSum.LightSubsetEnumerationSetup
end ThreeSum.LightSubsetEnumerationSetup
namespace ThreeSum.LightWeightDecode
end ThreeSum.LightWeightDecode
namespace ThreeSum.LightWeightGather
end ThreeSum.LightWeightGather
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCost
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCost
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRow
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRow
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightMaskBits
end ThreeSum1960614.Machine.ThreeSum.LightMaskBits
namespace ThreeSum1960614.Machine.ThreeSum.LightPairFlags
end ThreeSum1960614.Machine.ThreeSum.LightPairFlags
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup
end ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup
namespace ThreeSum1960614.Machine.ThreeSum.LightWeightDecode
end ThreeSum1960614.Machine.ThreeSum.LightWeightDecode
namespace ThreeSum1960614.Machine.ThreeSum.LightWeightGather
end ThreeSum1960614.Machine.ThreeSum.LightWeightGather
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.MaskErase
end ThreeSum1960614.Machine.ThreeSum.MaskErase
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-! # A literal Boolean coordinate row for a subset mask -/

namespace ThreeSum.LightMaskBits
open _root_.ThreeSum.LightMaskBits


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.MaskErase
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase

















variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem time_bound (L : ℕ) : _root_.ThreeSum.LightMaskBits.time L ≤ 300*(L+1)^2 := by
  unfold _root_.ThreeSum.LightMaskBits.time _root_.Light.powTableTime _root_.ThreeSum.LightMaskErase.time
  nlinarith

end ThreeSum.LightMaskBits

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing every candidate pair's key and trimming flag

All pairs of enumerated local vertices are visited. A zero coordinate-row
inner product tests disjointness; the two actual bucket counts determine
whether the pair survives. The local exhaustive scan is intentionally
unoptimized and its entire arithmetic and lookup cost is charged.
-/

namespace ThreeSum.LightPairFlags
open _root_.ThreeSum.LightPairFlags


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1500000
set_option maxRecDepth 5000















variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem time_bound (L n : ℕ) : _root_.ThreeSum.LightPairFlags.time L n ≤ 500*(n*n)*(L+n+1)+30 := by
  have hround : _root_.ThreeSum.LightPairFlags.roundTime L n+12 ≤ 500*(L+n+1) := by
    unfold _root_.ThreeSum.LightPairFlags.roundTime _root_.ThreeSum.LightBooleanDot.time _root_.ThreeSum.LightTrimTest.time
    omega
  have hmul := Nat.mul_le_mul_left (n*n) hround
  unfold _root_.ThreeSum.LightPairFlags.time
  nlinarith

end ThreeSum.LightPairFlags

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
# Actual decoding of the unchanged ordered hash-weight enumeration

The five-procedure program constructs its own power table, then decodes
the even and odd coordinates into two contiguous coefficient rows. The
digits are exactly those of `WeightEnumeration.decodedWeight`, which is
already proved equal to the original `allWeights` enumeration in order.
-/

namespace ThreeSum.LightWeightDecode
open _root_.ThreeSum.LightWeightDecode


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light










variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}











theorem time_bound (L k : ℕ) : _root_.ThreeSum.LightWeightDecode.time L k ≤ 600*(L+1)*(k+1) := by
  unfold _root_.ThreeSum.LightWeightDecode.time _root_.ThreeSum.LightWeightRow.time _root_.ThreeSum.LightRadixDigit.time _root_.Light.powTableTime
  nlinarith

end ThreeSum.LightWeightDecode

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Gathering selected coefficient rows

The selection array contains ordinary candidate indices. This fixed program
reads each selected index and copies its whole coefficient row into the
corresponding schedule occurrence. Repeated selections are retained.
-/

namespace ThreeSum.LightWeightGather
open _root_.ThreeSum.LightWeightGather


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1000000










variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem time_bound (rows width : ℕ) :
    _root_.ThreeSum.LightWeightGather.time rows width ≤ 130*(rows+1)*(width+1) := by
  unfold _root_.ThreeSum.LightWeightGather.time _root_.Light.copyTime
  nlinarith

end ThreeSum.LightWeightGather

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual construction of one retained local-cover row

The program constructs all pair keys and trimming flags, clears the output
row, and marks exactly the keys with retained representations. Repeated
representations are handled by the support operation. Earlier matrix rows
and inputs below the scratch boundary are preserved.
-/

namespace ThreeSum.LightLocalCoverRow
open _root_.ThreeSum.LightLocalCoverRow


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light







variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







theorem time_bound (L n p : ℕ) : _root_.ThreeSum.LightLocalCoverRow.time L n p ≤ 600*(n*n+1)*(L+n+p*p+1) := by
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.LightPairFlags.time_bound L n
  unfold _root_.ThreeSum.LightLocalCoverRow.time _root_.ThreeSum.LightSupportMark.time _root_.ThreeSum.LightSupportMark.markTime _root_.Light.fillTime
  nlinarith

end ThreeSum.LightLocalCoverRow

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

/-! # Polynomial bounds for the actual local-cover procedures -/

namespace ThreeSum.LightLocalCoverCost
open _root_.ThreeSum.LightLocalCoverCost


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout

set_option maxHeartbeats 1500000

theorem hash_time_bound (L n p : ℕ) :
    _root_.ThreeSum.LightHashHistogram.time L n p p ≤ 1000*(L+1)*(n+1)*(p+1) := by
  have hm := Nat.mul_le_mul_left n (Nat.log_le_self 2 (L*p+1))
  unfold _root_.ThreeSum.LightHashHistogram.time _root_.ThreeSum.LightMaskHashes.time _root_.ThreeSum.LightOneHot.time
    _root_.ThreeSum.LightResidues.residuesTime _root_.ThreeSum.LightResidues.residueBudget _root_.ThreeSum.LightHistogram.histogramTime
    _root_.ThreeSum.LightHistogram.countTime _root_.Light.powTableTime _root_.Light.fillTime
  ring_nf at hm ⊢
  omega

theorem greedy_time_bound (N C T : ℕ) :
    _root_.ThreeSum.LightCoverGreedy.time N C T ≤ 1000*(N+1)*(C+1)*(T+1) := by
  unfold _root_.ThreeSum.LightCoverGreedy.time _root_.ThreeSum.LightCoverGreedy.roundTime _root_.ThreeSum.LightCoverSelect.time
    _root_.ThreeSum.LightCoverScores.time _root_.ThreeSum.LightBooleanDot.time _root_.ThreeSum.LightMinimum.time _root_.ThreeSum.LightCoverUpdate.time _root_.Light.fillTime
  ring_nf
  omega

theorem mask_table_time_bound (L n : ℕ) :
    _root_.ThreeSum.LightMaskBitTable.time L n ≤ 400*(n+1)*(L+1)^2 := by
  have hm := Nat.mul_le_mul_left n (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskBits.time_bound L)
  have hs : n ≤ n*(L+1)^2 := Nat.le_mul_of_pos_right _ (by positivity)
  unfold _root_.ThreeSum.LightMaskBitTable.time
  ring_nf at hm hs ⊢
  omega

theorem candidate_time_bound {L n p N B : ℕ}
    (hB : 1 ≤ B) (hL : L+1 ≤ B) (hn : n+1 ≤ B) (hp : p+1 ≤ B) (hN : N+1 ≤ B) :
    _root_.ThreeSum.LightLocalCoverCandidate.time L n p N ≤ 5000*B^4 := by
  have hdecode : _root_.ThreeSum.LightWeightDecode.time L N ≤ 600*B^2 := by
    calc
      _ ≤ 600*(L+1)*(N+1) := _root_.ThreeSum1960614.Machine.ThreeSum.LightWeightDecode.time_bound L N
      _ ≤ 600*B*B := by gcongr
      _ = _ := by ring
  have hhash : _root_.ThreeSum.LightHashHistogram.time L n p p ≤ 1000*B^3 := by
    calc
      _ ≤ 1000*(L+1)*(n+1)*(p+1) := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCost.hash_time_bound L n p
      _ ≤ 1000*B*B*B := by gcongr
      _ = _ := by ring
  have hn2 : n*n+1 ≤ B^2 := by
    have hm := Nat.pow_le_pow_left hn 2
    nlinarith
  have hp2 : p*p ≤ B^2 := by
    have hm := Nat.pow_le_pow_left hp 2
    nlinarith
  have hB2 : B ≤ B^2 := Nat.le_self_pow (by decide) B
  have hrest : L+n+p*p+1 ≤ 3*B^2 := by omega
  have hrow : _root_.ThreeSum.LightLocalCoverRow.time L n p ≤ 1800*B^4 := by
    calc
      _ ≤ 600*(n*n+1)*(L+n+p*p+1) := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRow.time_bound L n p
      _ ≤ 600*(B^2)*(3*B^2) := Nat.mul_le_mul (Nat.mul_le_mul_left 600 hn2) hrest
      _ = _ := by ring
  have hb24 := Nat.pow_le_pow_right hB (by decide : 2 ≤ 4)
  have hb34 := Nat.pow_le_pow_right hB (by decide : 3 ≤ 4)
  have hb4 : 1 ≤ B^4 := Nat.pow_pos (by omega)
  unfold _root_.ThreeSum.LightLocalCoverCandidate.time
  omega

theorem matrix_time_bound {L n p N B : ℕ}
    (hB : 1 ≤ B) (hL : L+1 ≤ B) (hn : n+1 ≤ B) (hp : p+1 ≤ B) (hN : N+1 ≤ B) :
    _root_.ThreeSum.LightLocalCoverMatrix.time L n p N ≤ 6000*B^5 := by
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCost.candidate_time_bound hB hL hn hp hN
  have hm := Nat.mul_le_mul (show N ≤ B by omega) (Nat.add_le_add_right hc 200)
  have hb5 : B ≤ B^5 := Nat.le_self_pow (by decide) B
  have hb5' : 1 ≤ B^5 := Nat.pow_pos (by omega)
  unfold _root_.ThreeSum.LightLocalCoverMatrix.time
  ring_nf at hm ⊢
  omega

theorem host_time_bound {h B : ℕ}
    (hB : 1 ≤ B) (hL : 464*h+1 ≤ B) (hn : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h+1 ≤ B)
    (hp : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+1 ≤ B) (hN : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h+1 ≤ B) (hT : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h+1 ≤ B) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time h ≤ 8000*B^5 := by
  have hm := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCost.matrix_time_bound hB hL hn hp hN
  have hp2 : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h+1 ≤ B^2 := by
    have hs := Nat.pow_le_pow_left hp 2
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols
    nlinarith
  have hg : _root_.ThreeSum.LightCoverGreedy.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) ≤ 1000*B^4 := by
    calc
      _ ≤ 1000*(_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h+1)*(_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h+1)*(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h+1) := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCost.greedy_time_bound _ _ _
      _ ≤ 1000*B*(B^2)*B := by gcongr
      _ = _ := by ring
  have hh : _root_.ThreeSum.LightWeightGather.time (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (2*(464*h)) ≤ 260*B^2 := by
    calc
      _ ≤ 130*(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h+1)*(2*(464*h)+1) := _root_.ThreeSum1960614.Machine.ThreeSum.LightWeightGather.time_bound _ _
      _ ≤ 130*B*(2*B) := Nat.mul_le_mul (Nat.mul_le_mul_left 130 hT) (by omega)
      _ = _ := by ring
  have hb25 := Nat.pow_le_pow_right hB (by decide : 2 ≤ 5)
  have hb45 := Nat.pow_le_pow_right hB (by decide : 4 ≤ 5)
  have hb5 : 1 ≤ B^5 := Nat.pow_pos (by omega)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time
  change _root_.ThreeSum.LightLocalCoverMatrix.time (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h)+
    _root_.ThreeSum.LightCoverGreedy.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h)+
    _root_.ThreeSum.LightWeightGather.time (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (2*(464*h))+200 ≤ _
  omega



end ThreeSum.LightLocalCoverCost

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCost

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
set_option maxHeartbeats 1500000
section

theorem ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCost.build_time_bound__implementation_2a38b8183f {h B : ℕ}
    (hB : 1 ≤ B) (hL : 464*h+1 ≤ B) (hn : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h+1 ≤ B)
    (hp : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+1 ≤ B) (hN : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h+1 ≤ B) (hT : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h+1 ≤ B) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverBuild.time h ≤ 10000*B^5 := by
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCost.host_time_bound hB hL hn hp hN hT
  have he : _root_.ThreeSum.LightSubsetEnumerationSetup.time (464*h) h ≤ 800*B^2 := by
    calc
      _ ≤ 800*(464*h+1)*((464*h).choose h+1) := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup.time_bound _ _
      _ ≤ 800*B*B := Nat.mul_le_mul (Nat.mul_le_mul_left 800 hL) hn
      _ = _ := by ring
  have hb : _root_.ThreeSum.LightMaskBitTable.time (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h) ≤ 400*B^3 := by
    calc
      _ ≤ 400*(_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h+1)*(464*h+1)^2 := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCost.mask_table_time_bound _ _
      _ ≤ 400*B*(B^2) := by gcongr
      _ = _ := by ring
  have hb25 := Nat.pow_le_pow_right hB (by decide : 2 ≤ 5)
  have hb35 := Nat.pow_le_pow_right hB (by decide : 3 ≤ 5)
  have hb5 : 1 ≤ B^5 := Nat.pow_pos (by omega)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverBuild.time
  change _root_.ThreeSum.LightSubsetEnumerationSetup.time (464*h) h+
    _root_.ThreeSum.LightMaskBitTable.time (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h)+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time h+200 ≤ _
  omega
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCost.build_time_bound__implementation_2a38b8183f) := (@ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCost.build_time_bound__implementation_2a38b8183f)

#print axioms solution
