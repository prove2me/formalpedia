-- Prove2me | solution 1 for ThreeSum.LightBandPreprocessing.Represents.keep
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:46:45.311993+00:00
-- url     : https://prove2.me/submissions/b720414b-0047-4da6-8212-cd4bde2164eb

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








theorem At.keep {μ μ' : ℕ → ℤ} {lo hi bound : ℕ} {A : Family}
    (h : At μ lo hi A) (hk : Kept μ μ' bound)
    (hlo : lo+A.size ≤ bound) (hhi : hi+A.size ≤ bound) : At μ' lo hi A := by
  constructor
  · intro i hi
    rw [hk (lo+i) (by omega)]
    exact h.1 i hi
  · intro i hi'
    rw [hk (hi+i) (by omega)]
    exact h.2 i hi'
























































































































































































































































































































































end ThreeSum.LightBandEnumeration

end

section


/-!
# Closed normalization and band listing for three supplied color classes

The three class arrays are sorted and deduplicated separately. Their actual
length/count headers then drive the actual owner-table enumerator. The program
has twenty fixed procedures. No sorting function, lookup function, or band
enumerator is supplied by the caller.
-/

namespace ThreeSum.LightBandPreprocessing

open Light ThreeSum.BandPartition

set_option maxHeartbeats 1800000
set_option maxRecDepth 5000

variable {lim : Limits} {P : Program}





















theorem Represents.keep_sourceProof {μ μ' : ℕ → ℤ} {values endpoints g bound : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (h : Represents μ values endpoints g hg original L hs) (hk : Kept μ μ' bound)
    (hv : values+original.length ≤ bound) (he : endpoints+2+2*original.length ≤ bound) :
    Represents μ' values endpoints g hg original L hs := by
  obtain ⟨hseg,hn,hmem,hlen,hcount,hAt⟩ := h
  have hm := size_le L.length g
  refine ⟨?_,hn,hmem,?_,?_,?_⟩
  · intro i hi
    rw [hk (values+i) (by omega)]
    exact hseg i hi
  · rw [hk endpoints (by omega)]
    exact hlen
  · rw [hk (endpoints+1) (by omega)]
    exact hcount
  · exact hAt.keep hk (by change endpoints+2+size L.length g ≤ bound; omega)
      (by change endpoints+2+L.length+size L.length g ≤ bound; omega)











































































































































































































end ThreeSum.LightBandPreprocessing

end


theorem solution : ∀ {μ μ' : Nat → Int} {values endpoints g bound : Nat}
  {hg : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) g}
  {original L : List.{0} Int} {hs : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) L},
  ThreeSum.LightBandPreprocessing.Represents μ values endpoints g hg original L hs →
    Light.Kept μ μ' bound →
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) values (@List.length.{0} Int original))
          bound →
        @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) endpoints
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Int original)))
            bound →
          ThreeSum.LightBandPreprocessing.Represents μ' values endpoints g hg original L hs := by
  exact @ThreeSum.LightBandPreprocessing.Represents.keep_sourceProof

#print axioms solution
