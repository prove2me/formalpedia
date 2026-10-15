-- Prove2me | solution 1 for ThreeSum.ReportingHostPackedCatalog.upperBound_hit
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:09:54.172102+00:00
-- url     : https://prove2.me/submissions/b095e1cc-cb52-4b18-8e4f-0e20f24f5255

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
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
import Mathlib.Data.Finset.Basic
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
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
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
import Theorems.Thm_ThreeSum_BinarySearch_upperSearch_correct


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.ReportingHostPrefixCatalog
end ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum.ReportingHostPrefixOrder
end ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Executable binary search with a comparison budget

`upperSearch` finds the first array entry strictly above a query.  Its fuel is
logarithmic, and the proof accounts for the actual branches taken.  Array
accesses here are explicit function calls; a machine realization must still
implement those calls by bounded-address loads.
-/

namespace ThreeSum.BinarySearch













































































theorem upperBound_correct (f : ℕ → ℤ) (n : ℕ) (x : ℤ)
    (hsorted : ∀ i j, i ≤ j → j < n → f i ≤ f j) :
    Partition f x n (upperBound f n x) := by
  apply upperSearch_correct f x n (Nat.log 2 n + 1) 0 n hsorted (by omega) (by omega)
  · simpa only [Nat.sub_zero] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  · intro i hi; omega
  · intro i hi hin; omega

















































end ThreeSum.BinarySearch

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







theorem codes_length (key : ℕ → ℕ) (n : ℕ) : (codes key n).length=n := by simp [codes]























theorem packed_interval_unique {key : ℕ → ℕ} {n i j : ℕ}
    (hi : i < n) (hj : j < n)
    (hunique : ∀ a < n, ∀ b < n, key a=key b → a=b)
    (hlo : packed key n i ≤ packed key n j)
    (hhi : packed key n j ≤ key i*(n+1)+n) : i=j := by
  have hle : key i ≤ key j := by
    by_contra hh
    have hh' : key j+1 ≤ key i := by omega
    unfold packed at hlo
    nlinarith
  have hge : key j ≤ key i := by
    by_contra hh
    have hh' : key i+1 ≤ key j := by omega
    unfold packed at hhi
    nlinarith
  exact hunique i hi j hj (Nat.le_antisymm hle hge)

theorem sorted_getD_le {S : List ℤ} (hs : S.Pairwise (· ≤ ·)) :
    ∀ i j, i ≤ j → j < S.length → S.getD i 0 ≤ S.getD j 0 := by
  intro i j hij hj
  by_cases he : i=j
  · subst j; exact le_rfl
  · rw [List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ hj]
    exact List.pairwise_iff_getElem.mp hs i j (by omega) hj (by omega)

theorem upperBound_hit_sourceProof {key : ℕ → ℕ} {n i : ℕ} {S : List ℤ}
    (hi : i < n) (hunique : ∀ a < n, ∀ b < n, key a=key b → a=b)
    (hperm : S.Perm (codes key n)) (hs : S.Pairwise (· ≤ ·)) :
    let K := BinarySearch.upperBound (fun j => S.getD j 0) n ((key i*(n+1)+n : ℕ) : ℤ)
    0 < K ∧ K ≤ n ∧ S.getD (K-1) 0 = (packed key n i : ℤ) := by
  dsimp only
  have hlen : S.length=n := hperm.length_eq.trans (codes_length key n)
  have hsorted : ∀ a b, a ≤ b → b < n → S.getD a 0 ≤ S.getD b 0 := by
    simpa only [hlen] using sorted_getD_le hs
  have hpart := BinarySearch.upperBound_correct (fun j => S.getD j 0) n
    ((key i*(n+1)+n : ℕ) : ℤ) hsorted
  rcases hpart with ⟨hKn,hbelow,habove⟩
  have htarget : (packed key n i : ℤ) ∈ S := by
    apply hperm.mem_iff.mpr
    exact List.mem_ofFn.mpr ⟨⟨i,hi⟩,rfl⟩
  obtain ⟨j,hj,hjRead⟩ := List.mem_iff_getElem.mp htarget
  have hjn : j < n := by omega
  have hjRead' : S.getD j 0 = (packed key n i : ℤ) := by
    simpa only [List.getD_eq_getElem _ _ hj] using hjRead
  have htargetUpper : (packed key n i : ℤ) ≤ ((key i*(n+1)+n : ℕ) : ℤ) := by
    exact_mod_cast (show packed key n i ≤ key i*(n+1)+n by unfold packed; omega)
  have hjK : j < BinarySearch.upperBound (fun j => S.getD j 0) n ((key i*(n+1)+n : ℕ) : ℤ) := by
    by_contra hh
    have hx := habove j (by omega) hjn
    dsimp only at hx
    rw [hjRead'] at hx
    omega
  refine ⟨by omega,hKn,?_⟩
  have hlast : BinarySearch.upperBound (fun j => S.getD j 0) n ((key i*(n+1)+n : ℕ) : ℤ)-1 < n := by omega
  have hlast' : BinarySearch.upperBound (fun j => S.getD j 0) n ((key i*(n+1)+n : ℕ) : ℤ)-1 < S.length := by omega
  have hmem : S.getD (BinarySearch.upperBound (fun j => S.getD j 0) n
      ((key i*(n+1)+n : ℕ) : ℤ)-1) 0 ∈ S := by
    rw [List.getD_eq_getElem _ _ hlast']
    exact List.getElem_mem _
  obtain ⟨b,hb⟩ := List.mem_ofFn.mp (hperm.mem_iff.mp hmem)
  have hlo := hsorted j _ (by omega) hlast
  rw [hjRead',← hb] at hlo
  have hhi := hbelow _ (by omega : BinarySearch.upperBound (fun j => S.getD j 0) n
    ((key i*(n+1)+n : ℕ) : ℤ)-1 <
      BinarySearch.upperBound (fun j => S.getD j 0) n ((key i*(n+1)+n : ℕ) : ℤ))
  dsimp only at hhi
  rw [← hb] at hhi
  have he : i=b.val := packed_interval_unique hi b.isLt hunique (by exact_mod_cast hlo) (by exact_mod_cast hhi)
  exact hb.symm.trans (by rw [he])































end ThreeSum.ReportingHostPackedCatalog

end


theorem solution : ∀ {key : Nat → Nat} {n i : Nat} {S : List.{0} Int},
  @LT.lt.{0} Nat instLTNat i n →
    (∀ (a : Nat),
        @LT.lt.{0} Nat instLTNat a n →
          ∀ (b : Nat), @LT.lt.{0} Nat instLTNat b n → @Eq.{1} Nat (key a) (key b) → @Eq.{1} Nat a b) →
      @List.Perm.{0} Int S (ThreeSum.ReportingHostPackedCatalog.codes key n) →
        @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LE.le.{0} Int Int.instLEInt x1 x2) S →
          have K :=
            ThreeSum.BinarySearch.upperBound
              (fun (j : Nat) => @List.getD.{0} Int S j (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) n
              (@Nat.cast.{0} Int instNatCastInt
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (key i)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  n));
          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) K)
            (And (@LE.le.{0} Nat instLENat K n)
              (@Eq.{1} Int
                (@List.getD.{0} Int S
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) K
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
                (@Nat.cast.{0} Int instNatCastInt (ThreeSum.ReportingHostPackedCatalog.packed key n i)))) := by
  exact @ThreeSum.ReportingHostPackedCatalog.upperBound_hit_sourceProof

#print axioms solution
