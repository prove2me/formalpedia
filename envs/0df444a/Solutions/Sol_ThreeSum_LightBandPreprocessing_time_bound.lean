-- Prove2me | solution 1 for ThreeSum.LightBandPreprocessing.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:47:28.997615+00:00
-- url     : https://prove2.me/submissions/ae5b24c1-308e-4978-a403-5a063caf0597

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress

section


/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition





theorem size_le (n g : ℕ) : size n g ≤ n := by
  unfold size
  split_ifs with h
  · omega
  · have hdiv := Nat.div_le_self (n-1) g
    omega
































































































end ThreeSum.BandPartition

end

section


/-!
# Sorting and deduplicating a single already separated color class

The merge-sort implementation and proof are reused unchanged from the
attached upstream `ThreeSumApsp/Lang/Lib/Merge{,Sort}.lean` sources. The new
linear procedure removes adjacent repeats from the sorted output. The
original membership equivalence is retained, which is the witness needed
by the three-color reduction. Duplicates are removed only inside a class.
-/

namespace ThreeSum.LightNormalize

open Light

variable {lim : Limits} {P : Program}











































































































































































theorem time_bound (n : ℕ) : time n ≤ 400*(n+1)*(Nat.clog 2 n+1) := by
  have hsub : n-1 ≤ n := Nat.sub_le _ _
  unfold time sortTime dedupTime
  nlinarith

end ThreeSum.LightNormalize

end

section


/-!
# A closed machine program listing all relevant sorted-band candidates

The program computes its own binary width and power table, then executes
exactly the three rectangular owner tables. Every table cell contains an
interval lookup result (index plus one, zero for a miss). The source arrays
remain intact. The coverage theorem below connects these actual memory cells
to every relevant triple, and hence to every exact equation in the bands.
-/

namespace ThreeSum.LightBandEnumeration

set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

open Light ThreeSum.BandEnumeration ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}













































































































































































































































































































































theorem time_bound (nA nB nC : ℕ) :
    time nA nB nC ≤ 1000*(count nA nB nC+nA+nB+nC+1)*(width nA nB nC+1) := by
  have heq : time nA nB nC = count nA nB nC*(120*width nA nB nC+190)+
      76*(nB+2*nA)+29*width nA nB nC+553 := by
    unfold time clog2Time powTableTime LightBandTable.time LightBandTable.rowTime
      LightBandLookup.time LightBandLookup.searchTime count width
    ring
  rw [heq]
  generalize count nA nB nC = D
  generalize width nA nB nC = W
  nlinarith [Nat.zero_le (D*W),Nat.zero_le (nA*W),Nat.zero_le (nB*W),Nat.zero_le (nC*W)]


















end ThreeSum.LightBandEnumeration

end

section


/-!
# Normalizing one color class and constructing all its band endpoints

This closed eleven-procedure program joins the actual merge sort, adjacent
deduplication, quotient computation, and endpoint passes. It writes the
distinct-value length and band count in a two-cell header. The following
cells are the lower endpoints and, after the distinct-value length, the
upper endpoints. The membership witness still refers to the original class.
-/

namespace ThreeSum.LightSortedBands

open Light ThreeSum.BandPartition

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

variable {lim : Limits} {P : Program}





















































































































































































































theorem time_bound (n : ℕ) : time n ≤ 700*(n+1)*(Nat.clog 2 n+1) := by
  have h := LightNormalize.time_bound n
  unfold time
  nlinarith [Nat.zero_le (n*Nat.clog 2 n)]

end ThreeSum.LightSortedBands

end

section


/-!
# Finite bounds and original-value witness coverage for band preprocessing

These corollaries refer to the memory written by the closed twenty-procedure
program. An exact equation between members of the three original classes
produces a positive owner-table cell and three bands containing the values.
-/

namespace ThreeSum.LightBandPreprocessing

open Light ThreeSum.BandPartition









































































theorem time_bound_sourceProof (a b c g : ℕ) :
    time a b c g ≤
      2100*(a+b+c+1)*(Nat.clog 2 (a+b+c)+1)+
      1000*(LightBandEnumeration.count (size a g) (size b g) (size c g)+a+b+c+1)*
        (LightBandEnumeration.width (size a g) (size b g) (size c g)+1)+400 := by
  have hn (n : ℕ) (hn : n ≤ a+b+c) :
      LightSortedBands.time n ≤ 700*(a+b+c+1)*(Nat.clog 2 (a+b+c)+1) := by
    apply (LightSortedBands.time_bound n).trans
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 700 (by omega))
      (Nat.add_le_add_right (Nat.clog_mono_right 2 hn) 1)
  have ha := hn a (by omega)
  have hb := hn b (by omega)
  have hc := hn c (by omega)
  have henum := LightBandEnumeration.time_bound (size a g) (size b g) (size c g)
  have henum' : LightBandEnumeration.time (size a g) (size b g) (size c g) ≤
      1000*(LightBandEnumeration.count (size a g) (size b g) (size c g)+a+b+c+1)*
        (LightBandEnumeration.width (size a g) (size b g) (size c g)+1) := by
    apply henum.trans
    have hsum : size a g+size b g+size c g ≤ a+b+c :=
      Nat.add_le_add (Nat.add_le_add (size_le a g) (size_le b g)) (size_le c g)
    apply Nat.mul_le_mul_right
    apply Nat.mul_le_mul_left
    omega
  unfold time LightHeaderBands.time
  nlinarith










end ThreeSum.LightBandPreprocessing

end


theorem solution : ∀ (a b c g : Nat),
  @LE.le.{0} Nat instLENat (ThreeSum.LightBandPreprocessing.time a b c g)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2100) (instOfNatNat (nat_lit 2100)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a b) c)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (Nat.clog (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a b) c))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 1000) (instOfNatNat (nat_lit 1000)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ThreeSum.LightBandEnumeration.count (ThreeSum.BandPartition.size a g)
                      (ThreeSum.BandPartition.size b g) (ThreeSum.BandPartition.size c g))
                    a)
                  b)
                c)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (ThreeSum.LightBandEnumeration.width (ThreeSum.BandPartition.size a g) (ThreeSum.BandPartition.size b g)
              (ThreeSum.BandPartition.size c g))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@OfNat.ofNat.{0} Nat (nat_lit 400) (instOfNatNat (nat_lit 400)))) := by
  exact @ThreeSum.LightBandPreprocessing.time_bound_sourceProof

#print axioms solution
