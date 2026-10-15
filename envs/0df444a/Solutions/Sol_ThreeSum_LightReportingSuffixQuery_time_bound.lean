-- Prove2me | solution 1 for ThreeSum.LightReportingSuffixQuery.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:19:46.474862+00:00
-- url     : https://prove2.me/submissions/4b9b149c-3e93-4342-b075-9143304924c8

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
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
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
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
import Theorems.Thm_ThreeSum_SubsetAddress_enumerationWork_bound


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.MaskDifference
end ThreeSum.MaskDifference
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# A rectangular Pascal table in the benchmark language

Every coefficient is built once by addition from the preceding row.
The row-major representation supports one multiplication and two additions
per later lookup. No recursive binomial-coefficient evaluation is used.
-/

namespace ThreeSum.LightPascal

open Light

variable {lim : Limits} {P : Program} {d : ℕ}






















































































































































theorem buildTime_bound (L : ℕ) : buildTime L ≤ 1000*(L+1)^2 := by
  unfold buildTime rowTime LightArray.linearTime
  simp only [fillTime]
  nlinarith

end ThreeSum.LightPascal

end

section


/-!
# A complete subset-rank program, including table construction

This fixed program constructs both lookup tables in scratch and then ranks
one valid mask. Its cost is quadratic in the bit width. The faster cached
rank contract remains available separately, but no supplied table correctness
assumption appears in the fixed-program result below.
-/

namespace ThreeSum.LightSubsetSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}
















































































theorem time_bound (L : ℕ) : time L ≤ 1200*(L+1)^2 := by
  have hb := buildTime_bound L
  unfold time powTableTime rankTime
  nlinarith

end ThreeSum.LightSubsetSetup

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
# Computing the compact downset size

The program builds a Pascal table, scans all preceding layers, and adds
the final binomial coefficient. The table stride used by the transform
is therefore computed by an actual fixed program.
-/

namespace ThreeSum.LightDownsetSize

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}



















































































theorem time_bound (L : ℕ) : time L ≤ 1400*(L+1)^2 := by
  have hh := LightSubsetSetup.time_bound L
  have hp : 1 ≤ (L+1)^2 := Nat.one_le_pow' 2 L
  unfold time LightSubsetOffset.time
  nlinarith

end ThreeSum.LightDownsetSize

end

section


/-!
# A fixed program for the complete compact downset address

The input gives a mask and its known cardinality. The program constructs
its own Pascal and power tables, computes the layer rank, scans the layer
offset, and returns their sum. No table-correctness or algorithmic runtime
premise is supplied by the caller.
-/

namespace ThreeSum.LightDownsetAddress

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}







































































theorem time_bound (L : ℕ) : time L ≤ 1300*(L+1)^2 := by
  have h := LightSubsetSetup.time_bound L
  unfold time LightSubsetOffset.time
  nlinarith

end ThreeSum.LightDownsetAddress

end

section


/-!
# Executing a stored partial-zeta or box lookup

This fixed program computes the compact downset stride and the queried
subset rank from freshly built tables. It then reads exactly one stored
stage cell. The specialized contracts connect that machine read to the
forced-prefix sum and to the canonical sparse-box sum.
-/

namespace ThreeSum.LightStageLookup

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}










































































































theorem time_bound (L : ℕ) : time L ≤ 2800*(L+1)^2 := by
  have hs := LightDownsetSize.time_bound L
  have ha := LightDownsetAddress.time_bound L
  have hp : 1 ≤ (L+1)^2 := Nat.one_le_pow' 2 L
  unfold time
  omega

end ThreeSum.LightStageLookup

end

section


/-!
# Computing the least coordinate of a nonempty mask

The program constructs its own powers table, scans the bit positions,
and uses the verified mask-deletion test. Its work is quadratic in the
width and its scratch is linear. It never scans mask values.
-/

namespace ThreeSum.LightMaskMinimum

open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}
































































































































theorem time_bound (L : ℕ) : time L ≤ 500*(L+1)^2 := by
  unfold time powTableTime LightMaskErase.time
  nlinarith

end ThreeSum.LightMaskMinimum

end

section


/-!
# Executing a canonical sparse-query box

Given valid masks `U ⊆ Q`, the program subtracts their masks and
cardinalities, computes the least missing coordinate itself, computes
the compact stage address, and reads the signed box sum. The empty
missing set uses the final prefix stage. No address or minimum is
provided as advice.
-/

namespace ThreeSum.LightQueryBox

open Light ThreeSum.SubsetAddress ThreeSum.MaskDifference
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}



































































































































theorem time_bound (L : ℕ) : time L ≤ 3500*(L+1)^2 := by
  have hm := LightMaskMinimum.time_bound L
  have hl := LightStageLookup.time_bound L
  have hp : 1 ≤ (L+1)^2 := Nat.one_le_pow' 2 L
  unfold time
  omega

end ThreeSum.LightQueryBox

end

section


/-!
# Summing the canonical boxes of a sparse query

The missing-subset masks are loaded from an actual array, and every
summand is produced by the verified box-query procedure. Signed
accumulator bounds follow from bounds on the original leaf weights.
The final theorem identifies the sum with the canonical powerset-card
sum whenever the mask array is an exact enumeration of that family.
-/

namespace ThreeSum.LightBoxSum

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}











































































































































































theorem time_bound (L n : ℕ) : time L n ≤ 3600*(L+1)^2*(n+1) := by
  have h := LightQueryBox.time_bound L
  have hp : 1 ≤ (L+1)^2 := Nat.one_le_pow' 2 L
  have hb : LightQueryBox.time L+60 ≤ 3600*(L+1)^2 := by omega
  have hm := Nat.mul_le_mul_left n hb
  unfold time
  nlinarith

end ThreeSum.LightBoxSum

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
# Complete execution of the canonical box part of a sparse query

The query builds its own missing-subset array inside the actual query mask,
then evaluates every canonical box. Enumeration completeness and uniqueness
are discharged by the verified query-coordinate construction.
-/

namespace ThreeSum.LightCanonicalBoxSum

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open QueryCoordinates

variable {lim : Limits} {P : Program}



























































































































































theorem time_bound {W c t : ℕ} (hc : c ≤ W) :
    time W c t ≤ 5200*(W+1)^2*(c.choose t+1) := by
  have he := LightQueryEnumeration.time_bound (t := t) hc
  have hs := LightBoxSum.time_bound W (c.choose t)
  have hp : 1 ≤ (W+1)^2*(c.choose t+1) := Nat.mul_pos (by positivity) (by omega)
  unfold time
  nlinarith

end ThreeSum.LightCanonicalBoxSum

end

section


/-! # Actual output-sensitive enumeration and evaluation of explicit local suffix leaves -/

namespace ThreeSum.LightReportingSuffixExplicit

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open QueryCoordinates ReportingHostSuffix

variable {lim : Limits} {P : Program}





































































































































































theorem time_bound {W c t : ℕ} (ht : t ≤ W+1) :
    time W c t ≤ 11000*(W+1)^3*(layerOffset c t+1) := by
  have hp : 1 ≤ (W+1)^2*(layerOffset c t+1) := Nat.mul_pos (by positivity) (by omega)
  have hm := Nat.mul_le_mul_right (roundTime W c t+30) ht
  unfold time roundTime at *
  nlinarith

end ThreeSum.LightReportingSuffixExplicit

end

section


/-!
# The complete sparse query consumes suffix-local box tables

Explicit leaves use local output-sensitive enumeration and global source
reads; canonical boxes use only local-width compact addresses. The exact
finite partition yields the same global source Möbius value.
-/

namespace ThreeSum.LightReportingSuffixQuery

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix
open scoped BigOperators

variable {lim : Limits}























































































































































































theorem time_bound_sourceProof {W V c t : ℕ} (hV : V ≤ W) (hc : c ≤ V) (ht : t ≤ c+1) :
    time W V c t ≤ 17000*(W+1)^3*(LightSparseQuery.queryItems c t+1) := by
  have he := LightReportingSuffixExplicit.time_bound (c := c) (by omega : t ≤ W+1)
  have hb := LightCanonicalBoxSum.time_bound (t := t) hc
  have h₂₃ : (V+1)^2 ≤ (W+1)^3 :=
    (Nat.pow_le_pow_left (Nat.succ_le_succ hV) 2).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have ho : layerOffset c t+1 ≤ LightSparseQuery.queryItems c t+1 := by unfold LightSparseQuery.queryItems; omega
  have hh : c.choose t+1 ≤ LightSparseQuery.queryItems c t+1 := by unfold LightSparseQuery.queryItems; omega
  have he' := Nat.mul_le_mul_left (11000*(W+1)^3) ho
  have hb' := Nat.mul_le_mul (Nat.mul_le_mul_left 5200 h₂₃) hh
  have hpos : 1 ≤ (W+1)^3*(LightSparseQuery.queryItems c t+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hlin : V+1 ≤ (W+1)^3 := (Nat.succ_le_succ hV).trans
    (by simpa using (Nat.pow_le_pow_right (by omega : 1 ≤ W+1) (by decide : 1 ≤ 3)))
  have hm := Nat.le_mul_of_pos_right ((W+1)^3) (by omega : 0 < LightSparseQuery.queryItems c t+1)
  unfold time LightSign.time
  nlinarith

end ThreeSum.LightReportingSuffixQuery

end


theorem solution : ∀ {W V c t : Nat},
  @LE.le.{0} Nat instLENat V W →
    @LE.le.{0} Nat instLENat c V →
      @LE.le.{0} Nat instLENat t
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        @LE.le.{0} Nat instLENat (ThreeSum.LightReportingSuffixQuery.time W V c t)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 17000) (instOfNatNat (nat_lit 17000)))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.LightSparseQuery.queryItems c t)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  exact @ThreeSum.LightReportingSuffixQuery.time_bound_sourceProof

#print axioms solution
