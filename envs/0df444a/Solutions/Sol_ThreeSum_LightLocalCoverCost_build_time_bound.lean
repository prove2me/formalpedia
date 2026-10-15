-- Prove2me | solution 1 for ThreeSum.LightLocalCoverCost.build_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:19:41.359296+00:00
-- url     : https://prove2.me/submissions/749f20ff-a0db-4579-9bc8-4c0febd2c0c8

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
import Definitions.Def_ThreeSum1962Source_Bundle13
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
import Mathlib.Data.Finset.Card
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
import Mathlib.Data.List.Range
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
import Theorems.Thm_ThreeSum_SubsetAddress_enumerationWork_bound


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Actual decoding of the unchanged ordered hash-weight enumeration

The five-procedure program constructs its own power table, then decodes
the even and odd coordinates into two contiguous coefficient rows. The
digits are exactly those of `WeightEnumeration.decodedWeight`, which is
already proved equal to the original `allWeights` enumeration in order.
-/

namespace ThreeSum.LightWeightDecode

open Light


























variable {lim : Limits} {P : Program} {d : ℕ}



























































































theorem time_bound (L k : ℕ) : time L k ≤ 600*(L+1)*(k+1) := by
  unfold time LightWeightRow.time LightRadixDigit.time powTableTime
  nlinarith

end ThreeSum.LightWeightDecode

end

section


/-!
# Constructing every candidate pair's key and trimming flag

All pairs of enumerated local vertices are visited. A zero coordinate-row
inner product tests disjointness; the two actual bucket counts determine
whether the pair survives. The local exhaustive scan is intentionally
unoptimized and its entire arithmetic and lookup cost is charged.
-/

namespace ThreeSum.LightPairFlags

open Light

set_option maxHeartbeats 1500000
set_option maxRecDepth 5000



































variable {lim : Limits} {P : Program} {d : ℕ}






















































































































































































































theorem time_bound (L n : ℕ) : time L n ≤ 500*(n*n)*(L+n+1)+30 := by
  have hround : roundTime L n+12 ≤ 500*(L+n+1) := by
    unfold roundTime LightBooleanDot.time LightTrimTest.time
    omega
  have hmul := Nat.mul_le_mul_left (n*n) hround
  unfold time
  nlinarith

end ThreeSum.LightPairFlags

end

section


/-!
# Actual construction of one retained local-cover row

The program constructs all pair keys and trimming flags, clears the output
row, and marks exactly the keys with retained representations. Repeated
representations are handled by the support operation. Earlier matrix rows
and inputs below the scratch boundary are preserved.
-/

namespace ThreeSum.LightLocalCoverRow

open Light























variable {lim : Limits} {P : Program} {d : ℕ}










































































theorem time_bound (L n p : ℕ) : time L n p ≤ 600*(n*n+1)*(L+n+p*p+1) := by
  have ht := LightPairFlags.time_bound L n
  unfold time LightSupportMark.time LightSupportMark.markTime fillTime
  nlinarith

end ThreeSum.LightLocalCoverRow

end

section


/-! # A literal Boolean coordinate row for a subset mask -/

namespace ThreeSum.LightMaskBits

open Light LightSubsetAddress MaskErase































variable {lim : Limits} {P : Program} {d : ℕ}






















































































theorem time_bound (L : ℕ) : time L ≤ 300*(L+1)^2 := by
  unfold time powTableTime LightMaskErase.time
  nlinarith

end ThreeSum.LightMaskBits

end

section


/-!
# Gathering selected coefficient rows

The selection array contains ordinary candidate indices. This fixed program
reads each selected index and copies its whole coefficient row into the
corresponding schedule occurrence. Repeated selections are retained.
-/

namespace ThreeSum.LightWeightGather

open Light

set_option maxHeartbeats 1000000





















variable {lim : Limits} {P : Program} {d : ℕ}









































































theorem time_bound (rows width : ℕ) :
    time rows width ≤ 130*(rows+1)*(width+1) := by
  unfold time copyTime
  nlinarith

end ThreeSum.LightWeightGather

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


/-! # Polynomial bounds for the actual local-cover procedures -/

namespace ThreeSum.LightLocalCoverCost

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverLayout

set_option maxHeartbeats 1500000

theorem hash_time_bound (L n p : ℕ) :
    LightHashHistogram.time L n p p ≤ 1000*(L+1)*(n+1)*(p+1) := by
  have hm := Nat.mul_le_mul_left n (Nat.log_le_self 2 (L*p+1))
  unfold LightHashHistogram.time LightMaskHashes.time LightOneHot.time
    LightResidues.residuesTime LightResidues.residueBudget LightHistogram.histogramTime
    LightHistogram.countTime powTableTime fillTime
  ring_nf at hm ⊢
  omega

theorem greedy_time_bound (N C T : ℕ) :
    LightCoverGreedy.time N C T ≤ 1000*(N+1)*(C+1)*(T+1) := by
  unfold LightCoverGreedy.time LightCoverGreedy.roundTime LightCoverSelect.time
    LightCoverScores.time LightBooleanDot.time LightMinimum.time LightCoverUpdate.time fillTime
  ring_nf
  omega

theorem mask_table_time_bound (L n : ℕ) :
    LightMaskBitTable.time L n ≤ 400*(n+1)*(L+1)^2 := by
  have hm := Nat.mul_le_mul_left n (LightMaskBits.time_bound L)
  have hs : n ≤ n*(L+1)^2 := Nat.le_mul_of_pos_right _ (by positivity)
  unfold LightMaskBitTable.time
  ring_nf at hm hs ⊢
  omega

theorem candidate_time_bound {L n p N B : ℕ}
    (hB : 1 ≤ B) (hL : L+1 ≤ B) (hn : n+1 ≤ B) (hp : p+1 ≤ B) (hN : N+1 ≤ B) :
    LightLocalCoverCandidate.time L n p N ≤ 5000*B^4 := by
  have hdecode : LightWeightDecode.time L N ≤ 600*B^2 := by
    calc
      _ ≤ 600*(L+1)*(N+1) := LightWeightDecode.time_bound L N
      _ ≤ 600*B*B := by gcongr
      _ = _ := by ring
  have hhash : LightHashHistogram.time L n p p ≤ 1000*B^3 := by
    calc
      _ ≤ 1000*(L+1)*(n+1)*(p+1) := hash_time_bound L n p
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
  have hrow : LightLocalCoverRow.time L n p ≤ 1800*B^4 := by
    calc
      _ ≤ 600*(n*n+1)*(L+n+p*p+1) := LightLocalCoverRow.time_bound L n p
      _ ≤ 600*(B^2)*(3*B^2) := Nat.mul_le_mul (Nat.mul_le_mul_left 600 hn2) hrest
      _ = _ := by ring
  have hb24 := Nat.pow_le_pow_right hB (by decide : 2 ≤ 4)
  have hb34 := Nat.pow_le_pow_right hB (by decide : 3 ≤ 4)
  have hb4 : 1 ≤ B^4 := Nat.pow_pos (by omega)
  unfold LightLocalCoverCandidate.time
  omega

theorem matrix_time_bound {L n p N B : ℕ}
    (hB : 1 ≤ B) (hL : L+1 ≤ B) (hn : n+1 ≤ B) (hp : p+1 ≤ B) (hN : N+1 ≤ B) :
    LightLocalCoverMatrix.time L n p N ≤ 6000*B^5 := by
  have hc := candidate_time_bound hB hL hn hp hN
  have hm := Nat.mul_le_mul (show N ≤ B by omega) (Nat.add_le_add_right hc 200)
  have hb5 : B ≤ B^5 := Nat.le_self_pow (by decide) B
  have hb5' : 1 ≤ B^5 := Nat.pow_pos (by omega)
  unfold LightLocalCoverMatrix.time
  ring_nf at hm ⊢
  omega

theorem host_time_bound {h B : ℕ}
    (hB : 1 ≤ B) (hL : 512*h+1 ≤ B) (hn : vertices h+1 ≤ B)
    (hp : localPrime h+1 ≤ B) (hN : rows h+1 ≤ B) (hT : scheduleSize h+1 ≤ B) :
    LightLocalCoverHost.time h ≤ 8000*B^5 := by
  have hm := matrix_time_bound hB hL hn hp hN
  have hp2 : cols h+1 ≤ B^2 := by
    have hs := Nat.pow_le_pow_left hp 2
    unfold cols
    nlinarith
  have hg : LightCoverGreedy.time (rows h) (cols h) (scheduleSize h) ≤ 1000*B^4 := by
    calc
      _ ≤ 1000*(rows h+1)*(cols h+1)*(scheduleSize h+1) := greedy_time_bound _ _ _
      _ ≤ 1000*B*(B^2)*B := by gcongr
      _ = _ := by ring
  have hh : LightWeightGather.time (scheduleSize h) (2*(512*h)) ≤ 260*B^2 := by
    calc
      _ ≤ 130*(scheduleSize h+1)*(2*(512*h)+1) := LightWeightGather.time_bound _ _
      _ ≤ 130*B*(2*B) := Nat.mul_le_mul (Nat.mul_le_mul_left 130 hT) (by omega)
      _ = _ := by ring
  have hb25 := Nat.pow_le_pow_right hB (by decide : 2 ≤ 5)
  have hb45 := Nat.pow_le_pow_right hB (by decide : 4 ≤ 5)
  have hb5 : 1 ≤ B^5 := Nat.pow_pos (by omega)
  unfold LightLocalCoverHost.time
  change LightLocalCoverMatrix.time (512*h) (vertices h) (localPrime h) (rows h)+
    LightCoverGreedy.time (rows h) (cols h) (scheduleSize h)+
    LightWeightGather.time (scheduleSize h) (2*(512*h))+200 ≤ _
  omega

theorem build_time_bound_sourceProof {h B : ℕ}
    (hB : 1 ≤ B) (hL : 512*h+1 ≤ B) (hn : vertices h+1 ≤ B)
    (hp : localPrime h+1 ≤ B) (hN : rows h+1 ≤ B) (hT : scheduleSize h+1 ≤ B) :
    LightLocalCoverBuild.time h ≤ 10000*B^5 := by
  have hc := host_time_bound hB hL hn hp hN hT
  have he : LightSubsetEnumerationSetup.time (512*h) h ≤ 800*B^2 := by
    calc
      _ ≤ 800*(512*h+1)*((512*h).choose h+1) := LightSubsetEnumerationSetup.time_bound _ _
      _ ≤ 800*B*B := Nat.mul_le_mul (Nat.mul_le_mul_left 800 hL) hn
      _ = _ := by ring
  have hb : LightMaskBitTable.time (512*h) (vertices h) ≤ 400*B^3 := by
    calc
      _ ≤ 400*(vertices h+1)*(512*h+1)^2 := mask_table_time_bound _ _
      _ ≤ 400*B*(B^2) := by gcongr
      _ = _ := by ring
  have hb25 := Nat.pow_le_pow_right hB (by decide : 2 ≤ 5)
  have hb35 := Nat.pow_le_pow_right hB (by decide : 3 ≤ 5)
  have hb5 : 1 ≤ B^5 := Nat.pow_pos (by omega)
  unfold LightLocalCoverBuild.time
  change LightSubsetEnumerationSetup.time (512*h) h+
    LightMaskBitTable.time (512*h) (vertices h)+LightLocalCoverHost.time h+200 ≤ _
  omega

end ThreeSum.LightLocalCoverCost

end


theorem solution : ∀ {h B : Nat},
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) B →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        B →
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.LightLocalCoverLayout.vertices h)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          B →
        @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.LocalCoverBounds.localPrime h)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            B →
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.LightLocalCoverSchedule.rows h)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              B →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ThreeSum.GlobalEncoding.scheduleSize h)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                B →
              @LE.le.{0} Nat instLENat (ThreeSum.LightLocalCoverBuild.time h)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 10000) (instOfNatNat (nat_lit 10000)))
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) B
                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))) := by
  exact @ThreeSum.LightLocalCoverCost.build_time_bound_sourceProof

#print axioms solution
