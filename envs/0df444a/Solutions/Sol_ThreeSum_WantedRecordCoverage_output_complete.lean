-- Prove2me | solution 1 for ThreeSum.WantedRecordCoverage.output_complete
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:01:43.86344+00:00
-- url     : https://prove2.me/submissions/c03b8f83-cd62-4aaf-b18f-45abc2d11e6d

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle15
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
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.WantedRecordOrder
end ThreeSum.WantedRecordOrder

section


/-!
# Concrete integer indices for the local disjoint-subset graph

The finite list is the already checked layer-mask enumeration. Its Boolean
coordinate rows make disjointness an ordinary zero Boolean inner product.
-/

namespace ThreeSum.LocalMaskGraph

open Finset SubsetAddress MaskDecode
open scoped BigOperators
































theorem setAt_complete {L h : ℕ} (s : Finset (Fin L)) (hs : s.card=h) :
    ∃ i < vertexCount L h, setAt L h i=s := by
  have hm : subsetMask s ∈ enumerateLayer L h := (mem_enumerateLayer L h _).mpr (by
    simpa only [hs] using subsetMask_isMask s)
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
  refine ⟨i,by simpa [vertexCount,enumerateLayer_length] using hi,?_⟩
  unfold setAt maskAt
  rw [List.getD_eq_getElem _ _ hi,he,decode_subsetMask]




































end ThreeSum.LocalMaskGraph

end

section


/-!
# Literal global-output records behind the radix key array

Local records use the verified layer enumerator's order and retain every
schedule occurrence. Cartesian extension enumerates each original global
output once. Mapping to integers may introduce equal values; the key array
retains all of those separate incidences.
-/

namespace ThreeSum.GlobalKeyEnumeration

open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators

set_option maxHeartbeats 1800000











theorem layerRecord_surjective (h : ℕ) : Function.Surjective (layerRecord h) := by
  intro Q
  obtain ⟨i,hi,he⟩ := LocalMaskGraph.setAt_complete Q.val
    (LayerCounts.mem_vertices.mp Q.property)
  exact ⟨⟨i,hi⟩,Subtype.ext he⟩






theorem mem_layers (h : ℕ) (Q : {Q // Q ∈ LayerCounts.vertices (512*h) (2*h)}) :
    Q ∈ layers h := by
  obtain ⟨i,rfl⟩ := layerRecord_surjective h Q
  exact List.mem_ofFn.mpr ⟨i,rfl⟩














theorem mem_localRecords (h : ℕ) (b : OutputBlock h) : b ∈ localRecords h := by
  exact List.mem_product.mpr ⟨List.mem_finRange _,mem_layers h b.2⟩






















theorem mem_globalRecords (h J : ℕ) (q : GlobalOutput h J) :
    q ∈ globalRecords h J := by
  have hx : List.ofFn q ∈ tuples (localRecords h) J :=
    (mem_tuples _ _ _).mpr ⟨List.length_ofFn,fun b _ => mem_localRecords h b⟩
  apply List.mem_map.mpr
  refine ⟨⟨List.ofFn q,hx⟩,by simp,?_⟩
  funext i
  simp [tupleOfList]




























































end ThreeSum.GlobalKeyEnumeration

end

section


/-!
# Original A positions and all three guarded lifts

The physical key order is lift-major, preserving every original position.
The selected-offset count is transported to the unchanged guarded wanted
labels used by raw reporting, including repeated input values.
-/

namespace ThreeSum.RawAKeyLists

open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators

set_option maxHeartbeats 900000



















theorem mem_records (xs : List ℤ) (r : Record xs) : r ∈ records xs := by
  exact List.mem_product.mpr ⟨List.mem_finRange _,List.mem_finRange _⟩














































































































end ThreeSum.RawAKeyLists

end

section


/-!
# Completeness of the physical wanted-record array

The pair array produced by the selected-offset join covers every original
guarded wanted label. Conversely every stored pair selects such a label.
These statements concern the actual emitted array, including duplicate
integer keys at different source positions.
-/

namespace ThreeSum.WantedRecordCoverage

open Light GlobalEncoding GlobalKeyEnumeration WantedRecordOrder

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000

theorem label_surjective {xs : List ℤ} {h J : ℕ}
    (w : RawReporting.Wanted h J (Fin xs.length)) :
    ∃ i j, ∃ hi : i < 3*xs.length,
      j < LightGuardedWanted.totalKeys h J ∧ label h J i j hi=w := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp (RawAKeyLists.mem_records xs (w.2.1,w.1))
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp (mem_globalRecords h J w.2.2)
  have hi' : i.val < 3*xs.length := by
    simpa only [RawAKeyLists.records_length] using i.isLt
  have hj' : j.val < LightGuardedWanted.totalKeys h J := by
    have hj0 : j.val < OutputDecodeRecords.localCount h^J := by
      simpa only [OutputDecodeRecords.globalRecords_length'] using j.isLt
    exact hj0
  have hrec : (RawAKeyLists.records xs).getD i.val (0,⟨0,input_length_pos hi'⟩)=
      (w.2.1,w.1) := by
    simpa only [List.getD_eq_getElem _ _ i.isLt,List.get_eq_getElem] using hi
  rw [records_getD hi'] at hrec
  have hposition := congrArg (fun r : Fin 3 × Fin xs.length => r.2) hrec
  have hlift := congrArg (fun r : Fin 3 × Fin xs.length => r.1) hrec
  dsimp only at hposition hlift
  have hout : LightOutputDecodeOriginal.output h J j.val=w.2.2 := by
    simpa only [LightOutputDecodeOriginal.output,
      List.getD_eq_getElem _ _ j.isLt,List.get_eq_getElem] using hj
  refine ⟨i.val,j.val,hi',hj',?_⟩
  unfold label
  rw [hposition,hlift,hout]





















theorem output_complete_sourceProof {μ : ℕ → ℤ} {free M P h J : ℕ} {shift : ℤ} {xs : List ℤ}
    (H : LightWantedSetup.Output μ free M (LightGuardedWanted.left P xs)
      (LightGuardedWanted.right h J) (3*xs.length) (LightGuardedWanted.totalKeys h J) shift)
    {w : RawReporting.Wanted h J (Fin xs.length)}
    (hw : w ∈ RawAKeyLists.wanted M P xs h J shift) :
    ∃ slot i j, ∃ hi : i < 3*xs.length,
      slot < (μ free).toNat ∧ j < LightGuardedWanted.totalKeys h J ∧
      μ (LightWantedSetup.pairBase free (3*xs.length) (LightGuardedWanted.totalKeys h J) M+2*slot)=(i : ℤ) ∧
      μ (LightWantedSetup.pairBase free (3*xs.length) (LightGuardedWanted.totalKeys h J) M+2*slot+1)=(j : ℤ) ∧
      label h J i j hi=w := by
  obtain ⟨i,j,hi,hj,he⟩ := label_surjective w
  have hdiv := (mem_wanted_iff hi hj).mp (he.symm ▸ hw)
  rcases H with ⟨hcount,_,_,_,ps,hlen,_,hmem,hseg⟩
  have hp : (i,j) ∈ ps := (hmem i j).mpr ⟨hi,hj,hdiv⟩
  obtain ⟨k,hk⟩ := List.mem_iff_get.mp hp
  have hget : ps.getD k.val (0,0)=(i,j) := by
    simpa only [List.getD_eq_getElem _ _ k.isLt,List.get_eq_getElem] using hk
  have hread := segment_pair hseg k.isLt
  rw [hget] at hread
  refine ⟨k.val,i,j,hi,?_,hj,hread.1,hread.2,he⟩
  rw [hcount,Int.toNat_natCast,← hlen]
  exact k.isLt

end ThreeSum.WantedRecordCoverage

end


theorem solution : ∀ {μ : Nat → Int} {free M P h J : Nat} {shift : Int} {xs : List.{0} Int},
  ThreeSum.LightWantedSetup.Output μ free M (ThreeSum.LightGuardedWanted.left P xs)
      (ThreeSum.LightGuardedWanted.right h J)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@List.length.{0} Int xs))
      (ThreeSum.LightGuardedWanted.totalKeys h J) shift →
    ∀ {w : ThreeSum.RawReporting.Wanted.{0} h J (Fin (@List.length.{0} Int xs))},
      @Membership.mem.{0, 0} (ThreeSum.RawReporting.Wanted.{0} h J (Fin (@List.length.{0} Int xs)))
          (Finset.{0} (ThreeSum.RawReporting.Wanted.{0} h J (Fin (@List.length.{0} Int xs))))
          (@SetLike.instMembership.{0, 0}
            (Finset.{0} (ThreeSum.RawReporting.Wanted.{0} h J (Fin (@List.length.{0} Int xs))))
            (ThreeSum.RawReporting.Wanted.{0} h J (Fin (@List.length.{0} Int xs)))
            (@Finset.instSetLike.{0} (ThreeSum.RawReporting.Wanted.{0} h J (Fin (@List.length.{0} Int xs)))))
          (ThreeSum.RawAKeyLists.wanted M (@Nat.cast.{0} Int instNatCastInt P) xs h J shift) w →
        ∃ (slot : Nat) (i : Nat) (j : Nat) (hi :
          @LT.lt.{0} Nat instLTNat i
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@List.length.{0} Int xs))),
          And (@LT.lt.{0} Nat instLTNat slot (μ free).toNat)
            (And (@LT.lt.{0} Nat instLTNat j (ThreeSum.LightGuardedWanted.totalKeys h J))
              (And
                (@Eq.{1} Int
                  (μ
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (ThreeSum.LightWantedSetup.pairBase free
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@List.length.{0} Int xs))
                        (ThreeSum.LightGuardedWanted.totalKeys h J) M)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) slot)))
                  (@Nat.cast.{0} Int instNatCastInt i))
                (And
                  (@Eq.{1} Int
                    (μ
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (ThreeSum.LightWantedSetup.pairBase free
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@List.length.{0} Int xs))
                            (ThreeSum.LightGuardedWanted.totalKeys h J) M)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) slot))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@Nat.cast.{0} Int instNatCastInt j))
                  (@Eq.{1} (ThreeSum.RawReporting.Wanted.{0} h J (Fin (@List.length.{0} Int xs)))
                    (@ThreeSum.WantedRecordOrder.label xs h J i j hi) w)))) := by
  exact @ThreeSum.WantedRecordCoverage.output_complete_sourceProof

#print axioms solution
