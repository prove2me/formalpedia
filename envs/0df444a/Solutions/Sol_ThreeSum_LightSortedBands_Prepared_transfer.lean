-- Prove2me | solution 1 for ThreeSum.LightSortedBands.Prepared.transfer
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:47:03.79831+00:00
-- url     : https://prove2.me/submissions/44defe44-5a88-447b-bee4-b588bd6fda67

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle08
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
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition

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





























































































































































/-- Later stages may alter other memory, provided the value and endpoint
regions of this class are retained. -/
theorem Prepared.transfer_sourceProof {μ μ' : ℕ → ℤ} {values endpoints g : ℕ} {original : List ℤ}
    (h : Prepared μ values endpoints g original)
    (hk : ∀ a, (values ≤ a ∧ a < values+original.length) ∨
      (endpoints ≤ a ∧ a < endpoints+2+2*original.length) → μ' a = μ a) :
    Prepared μ' values endpoints g original := by
  obtain ⟨L,hL,hs,hn,hmem,hlen,hcount,hlo,hhi⟩ := h
  refine ⟨L,?_,hs,hn,hmem,?_,?_,?_,?_⟩
  · intro i hi
    rw [hk (values+i) (Or.inl (by omega))]
    exact hL i hi
  · rw [hk endpoints (Or.inr (by omega))]
    exact hlen
  · rw [hk (endpoints+1) (Or.inr (by omega))]
    exact hcount
  · intro i hi
    have hm := size_le L.length g
    rw [hk (endpoints+2+i) (Or.inr (by omega))]
    exact hlo i hi
  · intro i hi
    have hm := size_le L.length g
    rw [hk (endpoints+2+L.length+i) (Or.inr (by omega))]
    exact hhi i hi





































end ThreeSum.LightSortedBands

end


theorem solution : ∀ {μ μ' : Nat → Int} {values endpoints g : Nat} {original : List.{0} Int},
  ThreeSum.LightSortedBands.Prepared μ values endpoints g original →
    (∀ (a : Nat),
        Or
            (And (@LE.le.{0} Nat instLENat values a)
              (@LT.lt.{0} Nat instLTNat a
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) values
                  (@List.length.{0} Int original))))
            (And (@LE.le.{0} Nat instLENat endpoints a)
              (@LT.lt.{0} Nat instLTNat a
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) endpoints
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Int original))))) →
          @Eq.{1} Int (μ' a) (μ a)) →
      ThreeSum.LightSortedBands.Prepared μ' values endpoints g original := by
  exact @ThreeSum.LightSortedBands.Prepared.transfer_sourceProof

#print axioms solution
