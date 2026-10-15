-- Prove2me | solution 1 for ThreeSum.BandRawA.relevant_product_complete
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:05:00.473952+00:00
-- url     : https://prove2.me/submissions/bc0c7d3e-8f56-46c2-8176-5a23cb48b5d7

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
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
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
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
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
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
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
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
import Theorems.Thm_ThreeSum_BandEnumeration_Family_lookup_sound
import Theorems.Thm_ThreeSum_BandEnumeration_candidate_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_aIndices_iff_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_row
import Theorems.Thm_ThreeSum_BinarySearch_locate_complete


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress

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


































































































































































































































































theorem lookup_complete (A : Family) {i : ℕ} {x : ℤ} (hi : i < A.size)
    (hl : A.lower i ≤ x) (hh : x ≤ A.upper i) :
    LightBandLookup.result A.lower A.upper A.size x = i+1 := by
  have h := BinarySearch.locate_complete A.lower A.upper A.size x
    A.sorted A.separated hi hl hh
  simp [LightBandLookup.result,h]


































































































end ThreeSum.LightBandEnumeration

end

section


/-!
# The exact physical band-owner record order

There is one four-cell record for every owner-table cell, in BC, AB, AC
rectangle order. A zero flag is a lookup miss. Successful records retain
their physical owner slot even when several owners produce the same triple.
-/

namespace ThreeSum.BandCandidateRows

open BandEnumeration

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000



















































theorem rect_length (m n : ℕ) (F : ℕ → ℕ → Record) : (rect m n F).length=m*n := by
  simp [rect,List.length_flatMap]

theorem records_length (A B C : Family) :
    (records A B C).length=LightBandEnumeration.count A.size B.size C.size := by
  simp only [records,List.length_append,rect_length,LightBandEnumeration.count]
  omega







theorem index_lt {i j m n : ℕ} (hi : i < m) (hj : j < n) : i*n+j < m*n := by
  have hh := Nat.mul_le_mul_right n (show i+1 ≤ m by omega)
  simp only [Nat.add_mul,Nat.one_mul] at hh
  omega

theorem rect_getD {m n i j : ℕ} (F : ℕ → ℕ → Record) (hi : i < m) (hj : j < n) :
    (rect m n F).getD (i*n+j) default=F i j := by
  have hi' : i < (List.range m).length := by simpa using hi
  have hj' : j < (List.range n).length := by simpa using hj
  rw [rect,OutputDecodeOrder.getD_flatMap_uniform _ _ n (by simp) 0 default hi' hj]
  rw [List.getD_eq_getElem _ _ hi']
  simp only [List.getElem_range]
  rw [List.getD_map_of_lt _ hj' 0 default,List.getD_eq_getElem _ _ hj']
  simp only [List.getElem_range]

theorem slot_lt (A B C : Family) (o : Owner A B C) :
    slot A B C o < LightBandEnumeration.count A.size B.size C.size := by
  rcases o with ⟨j,k⟩ | ⟨i,j | k⟩
  · have hh := index_lt j.isLt k.isLt
    simp only [slot,LightBandEnumeration.count]
    omega
  · have hh := index_lt i.isLt j.isLt
    simp only [slot,LightBandEnumeration.count]
    omega
  · have hh := index_lt i.isLt k.isLt
    simp only [slot,LightBandEnumeration.count]
    omega

theorem records_getD_slot (A B C : Family) (o : Owner A B C) :
    (records A B C).getD (slot A B C o) default=fromOwner A B C o := by
  rcases o with ⟨j,k⟩ | ⟨i,j | k⟩
  · simp only [records,slot,fromOwner]
    rw [List.getD_append _ _ _ _ (by rw [rect_length]; exact index_lt j.isLt k.isLt)]
    exact rect_getD _ j.isLt k.isLt
  · simp only [records,slot,fromOwner]
    rw [List.getD_append_right _ _ _ _ (by rw [rect_length]; omega),rect_length]
    have hoff : B.size*C.size+i.val*B.size+j.val-B.size*C.size=i.val*B.size+j.val := by omega
    rw [hoff,List.getD_append _ _ _ _ (by rw [rect_length]; exact index_lt i.isLt j.isLt)]
    exact rect_getD _ i.isLt j.isLt
  · simp only [records,slot,fromOwner]
    rw [List.getD_append_right _ _ _ _ (by rw [rect_length]; omega),rect_length]
    have hoff : B.size*C.size+A.size*B.size+i.val*C.size+k.val-B.size*C.size=
        A.size*B.size+i.val*C.size+k.val := by omega
    rw [hoff,List.getD_append_right _ _ _ _ (by rw [rect_length]; omega),rect_length]
    have hoff' : A.size*B.size+i.val*C.size+k.val-A.size*B.size=i.val*C.size+k.val := by omega
    rw [hoff']
    exact rect_getD _ i.isLt k.isLt











































theorem lookup_result (A : Family) (x : ℤ) (i : A.Index) (hi : A.lookup x=some i) :
    LightBandLookup.result A.lower A.upper A.size x=i.val+1 :=
  LightBandEnumeration.lookup_complete A i.isLt (A.lookup_sound x i hi).1 (A.lookup_sound x i hi).2

theorem fromOwner_of_candidate (A B C : Family) (o : Owner A B C) (t : Triple A B C)
    (hc : candidate A B C o=some t) : fromOwner A B C o=fromTriple t := by
  rcases o with ⟨j,k⟩ | ⟨i,j | k⟩
  · simp only [candidate] at hc
    cases he : A.lookup (C.lo k-B.hi j) with
    | none => simp [he] at hc
    | some a =>
      have ht : (a,j,k)=t := by simpa only [he,Option.map_some,Option.some.injEq] using hc
      subst t
      have hr := lookup_result A _ a he
      change LightBandLookup.result A.lower A.upper A.size (C.lower k-B.upper j)=a.val+1 at hr
      simp [fromOwner,bc,make,hr,fromTriple]
  · simp only [candidate] at hc
    cases he : C.lookup (A.lo i+B.lo j) with
    | none => simp [he] at hc
    | some c =>
      have ht : (i,j,c)=t := by simpa only [he,Option.map_some,Option.some.injEq] using hc
      subst t
      have hr := lookup_result C _ c he
      change LightBandLookup.result C.lower C.upper C.size (A.lower i+B.lower j)=c.val+1 at hr
      simp [fromOwner,ab,make,hr,fromTriple]
  · simp only [candidate] at hc
    cases he : B.lookup (C.lo k-A.lo i) with
    | none => simp [he] at hc
    | some b =>
      have ht : (i,b,k)=t := by simpa only [he,Option.map_some,Option.some.injEq] using hc
      subst t
      have hr := lookup_result B _ b he
      change LightBandLookup.result B.lower B.upper B.size (C.lower k-A.lower i)=b.val+1 at hr
      simp [fromOwner,ac,make,hr,fromTriple]

theorem owner_covers (A B C : Family) (t : Triple A B C) (ht : relevant A B C t) :
    (records A B C).getD (slot A B C (owner A B C t)) default=fromTriple t := by
  rw [records_getD_slot]
  exact fromOwner_of_candidate A B C _ t (candidate_owner A B C t ht)










end ThreeSum.BandCandidateRows

end

section


/-!
# Exact A-value incidences of the physical band-owner catalog

Each successful owner contributes only its A band. Labels retain the
physical owner slot and the coordinate in the retained sorted A array.
Equal values and equal triples in different owner slots remain distinct.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows BandEnumeration BandPartition

set_option maxHeartbeats 1600000
set_option maxRecDepth 7000









































































































theorem mem_firstRows {n g i : ℕ} {rs : List Record} {l : Label} :
    l ∈ firstRows n g rs i ↔
      l.owner < i ∧ l ∈ row n g l.owner (rs.getD l.owner default) := by
  constructor
  · intro hl
    obtain ⟨owner,ho,hl⟩ := List.mem_flatMap.mp hl
    have he := (mem_row.mp hl).2.1
    subst owner
    exact ⟨List.mem_range.mp ho,hl⟩
  · rintro ⟨ho,hl⟩
    exact List.mem_flatMap.mpr ⟨l.owner,List.mem_range.mpr ho,hl⟩
















theorem label_covers {n g s p : ℕ} {rs : List Record}
    (hs : s < rs.length) (hf : (rs.getD s default).flag=1)
    (hp : start g (rs.getD s default).a ≤ p)
    (he : p < stop n g (rs.getD s default).a) :
    (⟨s,p⟩ : Label) ∈ items n g rs :=
  mem_firstRows.mpr ⟨hs,mem_row.mpr ⟨hf,rfl,hp,he⟩⟩

theorem owner_covers {A B C : Family} {n g p : ℕ} (t : Triple A B C)
    (ht : relevant A B C t) (hp : start g t.1.val ≤ p) (he : p < stop n g t.1.val) :
    (⟨slot A B C (owner A B C t),p⟩ : Label) ∈ items n g (records A B C) := by
  have hs : slot A B C (owner A B C t) < (records A B C).length := by
    rw [records_length]
    exact slot_lt A B C _
  have hr := BandCandidateRows.owner_covers A B C t ht
  apply label_covers hs
  · rw [hr]; rfl
  · simpa only [hr,fromTriple] using hp
  · simpa only [hr,fromTriple] using he














end ThreeSum.BandRawA

end

section


/-!
# Each physical A incidence retains exactly its owner's B/C product

The products in this file are mathematical counting domains. The actual
catalog is still constructed by the verified quadratic owner loop and
linear band copies. Distinct owner products are disjoint because their
physical A incidence indices differ, even when their values coincide.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1900000
set_option maxRecDepth 8000



























































theorem mem_ownerProduct {nA nB nC g s : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (hs : s < rs.length) :
    t ∈ ownerProduct nA nB nC g rs s ↔
      t.1 < (items nA g rs).length ∧ (labelAt nA g rs t.1).owner=s ∧
        t.2.1 ∈ bandPositions nB g (rs.getD s default).b ∧
        t.2.2 ∈ bandPositions nC g (rs.getD s default).c := by
  simp only [ownerProduct,mem_product,mem_aIndices_iff_owner hs,and_assoc]


































































/-- Every relevant original owner contributes all coordinates of its
actual band product. The returned A index is the physical flattened one. -/
theorem relevant_product_complete_sourceProof {A B C : BandEnumeration.Family}
    {nA nB nC g pA pB pC : ℕ} (t : BandEnumeration.Triple A B C)
    (ht : BandEnumeration.relevant A B C t)
    (ha : BandPartition.start g t.1.val ≤ pA ∧ pA < BandPartition.stop nA g t.1.val)
    (hb : BandPartition.start g t.2.1.val ≤ pB ∧ pB < BandPartition.stop nB g t.2.1.val)
    (hc : BandPartition.start g t.2.2.val ≤ pC ∧ pC < BandPartition.stop nC g t.2.2.val) :
    ∃ k < (items nA g (records A B C)).length,
      labelAt nA g (records A B C) k=⟨slot A B C (BandEnumeration.owner A B C t),pA⟩ ∧
      (k,pB,pC) ∈ ownerProduct nA nB nC g (records A B C)
        (slot A B C (BandEnumeration.owner A B C t)) := by
  have hlabel := owner_covers t ht ha.1 ha.2
  obtain ⟨k,hk,he⟩ := List.mem_iff_getElem.mp hlabel
  have heLabel : labelAt nA g (records A B C) k=
      ⟨slot A B C (BandEnumeration.owner A B C t),pA⟩ := by
    rw [labelAt,List.getD_eq_getElem _ _ hk,he]
  have hs : slot A B C (BandEnumeration.owner A B C t) < (records A B C).length := by
    rw [records_length]
    exact slot_lt A B C _
  have hr := BandCandidateRows.owner_covers A B C t ht
  refine ⟨k,hk,heLabel,(mem_ownerProduct hs).mpr ⟨hk,?_,?_,?_⟩⟩
  · rw [heLabel]
  · apply mem_bandPositions.mpr
    simpa only [hr,fromTriple] using hb
  · apply mem_bandPositions.mpr
    simpa only [hr,fromTriple] using hc

end ThreeSum.BandRawA

end


theorem solution : ∀ {A B C : ThreeSum.BandEnumeration.Family} {nA nB nC g pA pB pC : Nat} (t : ThreeSum.BandEnumeration.Triple A B C),
  ThreeSum.BandEnumeration.relevant A B C t →
    And
        (@LE.le.{0} Nat instLENat
          (ThreeSum.BandPartition.start g (@Fin.val A.size (@Prod.fst.{0, 0} A.Index (Prod.{0, 0} B.Index C.Index) t)))
          pA)
        (@LT.lt.{0} Nat instLTNat pA
          (ThreeSum.BandPartition.stop nA g
            (@Fin.val A.size (@Prod.fst.{0, 0} A.Index (Prod.{0, 0} B.Index C.Index) t)))) →
      And
          (@LE.le.{0} Nat instLENat
            (ThreeSum.BandPartition.start g
              (@Fin.val B.size
                (@Prod.fst.{0, 0} B.Index C.Index (@Prod.snd.{0, 0} A.Index (Prod.{0, 0} B.Index C.Index) t))))
            pB)
          (@LT.lt.{0} Nat instLTNat pB
            (ThreeSum.BandPartition.stop nB g
              (@Fin.val B.size
                (@Prod.fst.{0, 0} B.Index C.Index (@Prod.snd.{0, 0} A.Index (Prod.{0, 0} B.Index C.Index) t))))) →
        And
            (@LE.le.{0} Nat instLENat
              (ThreeSum.BandPartition.start g
                (@Fin.val C.size
                  (@Prod.snd.{0, 0} B.Index C.Index (@Prod.snd.{0, 0} A.Index (Prod.{0, 0} B.Index C.Index) t))))
              pC)
            (@LT.lt.{0} Nat instLTNat pC
              (ThreeSum.BandPartition.stop nC g
                (@Fin.val C.size
                  (@Prod.snd.{0, 0} B.Index C.Index (@Prod.snd.{0, 0} A.Index (Prod.{0, 0} B.Index C.Index) t))))) →
          ∃ (k : Nat),
            And
              (@LT.lt.{0} Nat instLTNat k
                (@List.length.{0} ThreeSum.BandRawA.Label
                  (ThreeSum.BandRawA.items nA g (ThreeSum.BandCandidateRows.records A B C))))
              (And
                (@Eq.{1} ThreeSum.BandRawA.Label
                  (ThreeSum.BandRawA.labelAt nA g (ThreeSum.BandCandidateRows.records A B C) k)
                  { owner := ThreeSum.BandCandidateRows.slot A B C (ThreeSum.BandEnumeration.owner A B C t),
                    position := pA })
                (@Membership.mem.{0, 0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))
                  (Finset.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)))
                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)))
                    (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))
                    (@Finset.instSetLike.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))))
                  (ThreeSum.BandRawA.ownerProduct nA nB nC g (ThreeSum.BandCandidateRows.records A B C)
                    (ThreeSum.BandCandidateRows.slot A B C (ThreeSum.BandEnumeration.owner A B C t)))
                  (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat Nat) k (@Prod.mk.{0, 0} Nat Nat pB pC)))) := by
  exact @ThreeSum.BandRawA.relevant_product_complete_sourceProof

#print axioms solution
