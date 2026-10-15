-- Prove2me | solution 1 for ThreeSum.LocalMaskHashes.indexed_bucket_count
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:12:14.570355+00:00
-- url     : https://prove2.me/submissions/502befb5-d9b7-4f2e-b480-133d45acc7f3

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
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
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
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
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Theorems.Thm_ThreeSum_SubsetAddress_enumerateLayer_nodup


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.LocalMaskGraph
end ThreeSum.LocalMaskGraph
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Concrete integer indices for the local disjoint-subset graph

The finite list is the already checked layer-mask enumeration. Its Boolean
coordinate rows make disjointness an ordinary zero Boolean inner product.
-/

namespace ThreeSum.LocalMaskGraph

open Finset SubsetAddress MaskDecode
open scoped BigOperators












theorem maskAt_spec {L h i : ℕ} (hi : i < vertexCount L h) :
    IsMask L h (maskAt L h i) := (mem_enumerateLayer L h _).mp (maskAt_mem hi)




theorem subsetMask_setAt {L h i : ℕ} (hi : i < vertexCount L h) :
    subsetMask (setAt L h i) = maskAt L h i := subsetMask_decode (maskAt_spec hi).1

theorem maskAt_injective {L h i j : ℕ} (hi : i < vertexCount L h) (hj : j < vertexCount L h)
    (he : maskAt L h i = maskAt L h j) : i=j := by
  have hi' : i < (enumerateLayer L h).length := by simpa [vertexCount,enumerateLayer_length] using hi
  have hj' : j < (enumerateLayer L h).length := by simpa [vertexCount,enumerateLayer_length] using hj
  exact (List.getD_inj hi' hj' (enumerateLayer_nodup L h)).mp he

theorem setAt_injective {L h i j : ℕ} (hi : i < vertexCount L h) (hj : j < vertexCount L h)
    (he : setAt L h i = setAt L h j) : i=j := by
  apply maskAt_injective hi hj
  rw [← subsetMask_setAt hi,← subsetMask_setAt hj,he]

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
# Exact hash codes and bucket counts for enumerated local vertices

The finite graph used in the moment proof is identified with the literal
mask list consumed by the machine.  In particular, the machine histogram
counts exactly the graph's endpoint buckets, including multiplicities.
-/

namespace ThreeSum.LocalMaskHashes

open Finset LocalMaskGraph LocalHashMoments LocalCoverBounds

variable {h L k : ℕ}





















































theorem indexed_bucket_count_sourceProof (w : Weight L (LocalField h))
    (shape : Finset (Fin L) → (Fin L → Bool)) (hinj : Function.Injective shape)
    (code : ℕ → ℕ)
    (hcodeLt : ∀ i < LocalMaskGraph.vertexCount L k, code i < localPrime h)
    (hcode : ∀ i < LocalMaskGraph.vertexCount L k,
      (code i : LocalField h) = HashFamily.hashValue w (shape (setAt L k i)))
    {r : ℕ} (hr : r < localPrime h) :
    LightHistogram.count code r (LocalMaskGraph.vertexCount L k) =
      HashFamily.bucketSize ((LayerCounts.vertices L k).image shape) w (r : LocalField h) := by
  unfold LightHistogram.count HashFamily.bucketSize
  apply card_bij (fun i _ => shape (setAt L k i))
  · intro i hi
    obtain ⟨hi,hci⟩ := mem_filter.mp hi
    have hi' := mem_range.mp hi
    refine mem_filter.mpr ⟨mem_image.mpr ⟨setAt L k i,
      LayerCounts.mem_vertices.mpr (setAt_card hi'),rfl⟩,?_⟩
    rw [← hcode i hi',hci]
  · intro i hi j hj he
    exact setAt_injective (mem_range.mp (mem_filter.mp hi).1)
      (mem_range.mp (mem_filter.mp hj).1) (hinj he)
  · intro s hs
    obtain ⟨hs,hhash⟩ := mem_filter.mp hs
    obtain ⟨S,hS,rfl⟩ := mem_image.mp hs
    obtain ⟨i,hi,he⟩ := setAt_complete S (LayerCounts.mem_vertices.mp hS)
    have hcast : (code i : LocalField h) = (r : LocalField h) := by
      rw [hcode i hi,he]
      exact hhash
    have hci : code i = r := by
      have hv := congrArg ZMod.val hcast
      simpa only [ZMod.val_natCast_of_lt (hcodeLt i hi),ZMod.val_natCast_of_lt hr] using hv
    exact ⟨i,mem_filter.mpr ⟨mem_range.mpr hi,hci⟩,congrArg shape he⟩













end ThreeSum.LocalMaskHashes

end


theorem solution : ∀ {h L k : Nat} (w : ThreeSum.LocalHashMoments.Weight.{0} L (ThreeSum.LocalHashMoments.LocalField h))
  (shape : Finset.{0} (Fin L) → Fin L → Bool),
  @Function.Injective.{1, 1} (Finset.{0} (Fin L)) (Fin L → Bool) shape →
    ∀ (code : Nat → Nat),
      (∀ (i : Nat),
          @LT.lt.{0} Nat instLTNat i (ThreeSum.LocalMaskGraph.vertexCount L k) →
            @LT.lt.{0} Nat instLTNat (code i) (ThreeSum.LocalCoverBounds.localPrime h)) →
        (∀ (i : Nat),
            @LT.lt.{0} Nat instLTNat i (ThreeSum.LocalMaskGraph.vertexCount L k) →
              @Eq.{1} (ThreeSum.LocalHashMoments.LocalField h)
                (@Nat.cast.{0} (ThreeSum.LocalHashMoments.LocalField h)
                  (@AddMonoidWithOne.toNatCast.{0} (ThreeSum.LocalHashMoments.LocalField h)
                    (@AddGroupWithOne.toAddMonoidWithOne.{0} (ThreeSum.LocalHashMoments.LocalField h)
                      (@Ring.toAddGroupWithOne.{0} (ThreeSum.LocalHashMoments.LocalField h)
                        (@DivisionRing.toRing.{0} (ThreeSum.LocalHashMoments.LocalField h)
                          (@Field.toDivisionRing.{0} (ThreeSum.LocalHashMoments.LocalField h)
                            (@ZMod.instField (ThreeSum.LocalCoverBounds.localPrime h)
                              (ThreeSum.LocalHashMoments.localPrimeFact h)))))))
                  (code i))
                (@ThreeSum.HashFamily.hashValue.{0, 0} (Fin L) (ThreeSum.LocalHashMoments.LocalField h) (Fin.fintype L)
                  (@ZMod.instField (ThreeSum.LocalCoverBounds.localPrime h)
                    (ThreeSum.LocalHashMoments.localPrimeFact h))
                  w (shape (ThreeSum.LocalMaskGraph.setAt L k i)))) →
          ∀ {r : Nat},
            @LT.lt.{0} Nat instLTNat r (ThreeSum.LocalCoverBounds.localPrime h) →
              @Eq.{1} Nat (ThreeSum.LightHistogram.count code r (ThreeSum.LocalMaskGraph.vertexCount L k))
                (@ThreeSum.HashFamily.bucketSize.{0, 0} (Fin L) (ThreeSum.LocalHashMoments.LocalField h) (Fin.fintype L)
                  (@ZMod.instField (ThreeSum.LocalCoverBounds.localPrime h)
                    (ThreeSum.LocalHashMoments.localPrimeFact h))
                  (ZMod.decidableEq (ThreeSum.LocalCoverBounds.localPrime h))
                  (@Finset.image.{0, 0} (Finset.{0} (Fin L)) (Fin L → Bool)
                    (fun (a b : Fin L → Bool) =>
                      @Fintype.decidablePiFintype.{0, 0} (Fin L) (fun (a : Fin L) => Bool)
                        (fun (a : Fin L) => instDecidableEqBool) (Fin.fintype L) a b)
                    shape (ThreeSum.LayerCounts.vertices L k))
                  w
                  (@Nat.cast.{0} (ThreeSum.LocalHashMoments.LocalField h)
                    (@AddMonoidWithOne.toNatCast.{0} (ThreeSum.LocalHashMoments.LocalField h)
                      (@AddGroupWithOne.toAddMonoidWithOne.{0} (ThreeSum.LocalHashMoments.LocalField h)
                        (@Ring.toAddGroupWithOne.{0} (ThreeSum.LocalHashMoments.LocalField h)
                          (@DivisionRing.toRing.{0} (ThreeSum.LocalHashMoments.LocalField h)
                            (@Field.toDivisionRing.{0} (ThreeSum.LocalHashMoments.LocalField h)
                              (@ZMod.instField (ThreeSum.LocalCoverBounds.localPrime h)
                                (ThreeSum.LocalHashMoments.localPrimeFact h)))))))
                    r)) := by
  exact @ThreeSum.LocalMaskHashes.indexed_bucket_count_sourceProof

#print axioms solution
