-- Prove2me | solution 1 for ThreeSum.LightBlockChildrenIndexed.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:32:00.879224+00:00
-- url     : https://prove2.me/submissions/13945cfc-cb14-4200-a58f-cd336788939b

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
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
import Theorems.Thm_ThreeSum_LightBlockChildren_meets
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_localRow
import Theorems.Thm_ThreeSum_ReportingHostMasks_prefixRows_append
import Theorems.Thm_ThreeSum_ReportingHostMasks_querySet_step


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Flattening a block family of subsets

The coordinates retain the block index explicitly. Joining and slicing are
mutually inverse, preserve Boolean set operations, and give exact cardinalities
for balanced full inputs and forced prefixes.
-/

namespace ThreeSum.BlockRows

open Finset
open scoped BigOperators











@[simp] theorem mem_join {J L : ℕ} {I : Finset (Fin J)}
    {u : Fin J → Finset (Fin L)} {i : Fin J} {x : Fin L} :
    Sigma.mk i x ∈ join I u ↔ i ∈ I ∧ x ∈ u i := Finset.mem_sigma




























































theorem join_card {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    (join I u).card = ∑ i ∈ I, (u i).card := Finset.card_sigma _ _



















@[simp] theorem mem_prefixIndices {J k : ℕ} {i : Fin J} :
    i ∈ prefixIndices J k ↔ i.val < k := by simp [prefixIndices]



















end ThreeSum.BlockRows

end

section


/-!
# Explicit row-major encoding of the block ground set

Block coordinates are numbered by `block * width + coordinate`. The
equivalence connects compact machine-mask tables on `Fin (J*L)` with the
sigma-typed block sets in the reporting proof. Flattened one-hot coefficients
already include their positional radix factors.
-/

namespace ThreeSum.BlockIndex

open Finset BlockRows BlockEncoding GlobalEncoding LocalHashMoments LocalCoverBounds
open scoped BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false




@[simp] theorem coordEquiv_val {J L : ℕ} (i : Fin J) (x : Fin L) :
    (coordEquiv J L ⟨i,x⟩).val = i.val*L+x.val := by
  simp [coordEquiv, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]







@[simp] theorem mem_indexSet {J L : ℕ} (S : Finset (Coord J L)) (c : Coord J L) :
    coordEquiv J L c ∈ indexSet S ↔ c ∈ S := by
  simp [indexSet]

@[simp] theorem indexSet_card {J L : ℕ} (S : Finset (Coord J L)) :
    (indexSet S).card = S.card := Finset.card_map _


































































































end ThreeSum.BlockIndex

end

section


/-! # Exact arithmetic subtraction of one subset mask from another -/

namespace ThreeSum.MaskDifference

open Finset ThreeSum.SubsetAddress

theorem subsetMask_sum {L : ℕ} (S : Finset (Fin L)) :
    subsetMask S = ∑ i ∈ S, 2^i.val := by
  simp [subsetMask,maskOf,natPositions]














































end ThreeSum.MaskDifference

end

section


/-! # Exact row-major mask packing and prefix scan invariants -/

namespace ThreeSum.BlockMaskLayout

open Finset BlockRows BlockIndex ThreeSum.SubsetAddress
open scoped BigOperators







theorem mask_join {J L : ℕ} (I : Finset (Fin J)) (rows : Fin J → Finset (Fin L)) :
    subsetMask (indexSet (join I rows)) = ∑ i ∈ I, rowMask rows i := by
  rw [MaskDifference.subsetMask_sum]
  unfold indexSet
  rw [Finset.sum_map]
  unfold join
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Equiv.toEmbedding_apply,coordEquiv_val,pow_add,rowMask,
    MaskDifference.subsetMask_sum,Finset.mul_sum]






















































end ThreeSum.BlockMaskLayout

end

section


/-!
# Exact next-block masks for the reporting host

The machine enumerates subsets directly in the global row-major ground set.
This file identifies those subsets with the balanced next-row children of
the original reporting tree, and proves the arithmetic mask transitions.
-/

namespace ThreeSum.ReportingHostMasks

open Finset BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open ThreeSum.SubsetAddress StoredReporting BlockForced




@[simp] theorem mem_blockSet {J L : ℕ} (i j : Fin J) (S : Finset (Fin L)) (x : Fin L) :
    coordEquiv J L ⟨j,x⟩ ∈ blockSet i S ↔ j = i ∧ x ∈ S := by
  simp [blockSet]

@[simp] theorem blockSet_card {J L : ℕ} (i : Fin J) (S : Finset (Fin L)) :
    (blockSet i S).card = S.card := by
  simp [blockSet,join_card]

@[simp] theorem blockSet_mask {J L : ℕ} (i : Fin J) (S : Finset (Fin L)) :
    subsetMask (blockSet i S) = 2^(i.val*L)*subsetMask S := by
  simp [blockSet,mask_join,rowMask]

















































































theorem leftPrefix_step {J L k : ℕ} (u : Fin J → Finset (Fin L)) (hk : k < J)
    (S : Finset (Fin L)) :
    leftPrefix (k+1) (Function.update u ⟨k,hk⟩ S) =
      leftPrefix k u ∪ blockSet ⟨k,hk⟩ S := by
  ext x
  obtain ⟨⟨i,a⟩,rfl⟩ := (coordEquiv J L).surjective x
  simp only [leftPrefix,prefixLeft,mem_indexSet,mem_join,mem_prefixIndices,
    Finset.mem_union,mem_blockSet]
  by_cases he : i = ⟨k,hk⟩
  · subst i
    simp
  · have hv : i.val ≠ k := fun h => he (Fin.ext h)
    have hi : i.val < k+1 ↔ i.val < k := by omega
    simp [he,hi]

theorem prefix_disjoint_block {J L k : ℕ} (u : Fin J → Finset (Fin L)) (hk : k < J)
    (S : Finset (Fin L)) : Disjoint (leftPrefix k u) (blockSet ⟨k,hk⟩ S) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨⟨i,a⟩,rfl⟩ := (coordEquiv J L).surjective x
  obtain ⟨rfl,_⟩ := (mem_blockSet _ _ _ _).mp hy
  have hh := (mem_join.mp (mem_indexSet _ _ |>.mp hx)).1
  exact (by simp : (⟨k,hk⟩ : Fin J) ∉ prefixIndices J k) hh

theorem rightPrefix_step {J L k : ℕ} (Q u : Fin J → Finset (Fin L)) (hk : k < J)
    (S : Finset (Fin L)) :
    rightPrefix (k+1) Q (Function.update u ⟨k,hk⟩ S) =
      rightPrefix k Q u ∪ blockSet ⟨k,hk⟩ (Q ⟨k,hk⟩ \ S) := by
  have he : (fun i => Q i \ Function.update u ⟨k,hk⟩ S i) =
      Function.update (fun i => Q i \ u i) ⟨k,hk⟩ (Q ⟨k,hk⟩ \ S) := by
    funext i
    by_cases hi : i = ⟨k,hk⟩
    · subst i; simp
    · simp [hi]
  change leftPrefix (k+1) (fun i => Q i \ Function.update u ⟨k,hk⟩ S i) = _
  rw [he,leftPrefix_step]
  rfl













































theorem blockSet_subset_query {J L k : ℕ} (Q : Fin J → Finset (Fin L)) (hk : k < J) :
    blockSet ⟨k,hk⟩ (Q ⟨k,hk⟩) ⊆ querySet k Q := by
  intro x hx
  obtain ⟨⟨i,a⟩,rfl⟩ := (coordEquiv J L).surjective x
  obtain ⟨rfl,ha⟩ := (mem_blockSet _ _ _ _).mp hx
  simp only [querySet,mem_indexSet,remaining,mem_join,Finset.mem_compl,mem_prefixIndices]
  exact ⟨by simp,ha⟩

























































end ThreeSum.ReportingHostMasks

end

section


/-!
# Actual construction of every next-block reporting child

The fixed program enumerates the balanced subsets of the next block directly
in global coordinates. Two affine scans then write the exact left and right
prefix masks of every child, and subtraction returns the next residual mask.
All enumeration and scan execution is discharged by concrete procedures.
-/

namespace ThreeSum.LightBlockChildren

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open QueryCoordinates ReportingHostMasks

variable {lim : Limits} {P : Program}








































































































































theorem program_meets {μ : ℕ → ℤ} {W h masks dstL dstR work d : ℕ}
    (A B Q R : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hAQ : Disjoint A Q) (hBQ : Disjoint B Q) (hQR : Q ⊆ R)
    (hh : h ≤ Q.card+1)
    (hmasks : masks+Q.card.choose h ≤ dstL)
    (hleft : dstL+Q.card.choose h ≤ dstR)
    (hright : dstR+Q.card.choose h ≤ work)
    (hspace : work+(2*W+2) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+W+3 ≤ lim.depth) :
    Meets lim program 0 d
      [W,h,subsetMask Q,subsetMask A,subsetMask B,subsetMask R,masks,dstL,dstR,work]
      μ (time W Q.card h)
      (fun r μ' =>
        r = (subsetMask (R \ Q) : ℤ) ∧
        SegN μ' masks ((missingSets Q h).map subsetMask) ∧
        SegN μ' dstL (leftMasks A Q h) ∧
        SegN μ' dstR (rightMasks B Q h) ∧ Kept μ μ' masks) :=
  meets rfl procs A B Q R hw hAQ hBQ hQR hh hmasks hleft hright hspace hword hd








end ThreeSum.LightBlockChildren

end

section


/-! # The concrete child constructor extends the original valid reporting prefixes -/

namespace ThreeSum.LightBlockChildrenIndexed

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open BlockRows BlockIndex BlockMaskLayout BlockIndexedQuery BlockForced StoredReporting
open ReportingHostMasks QueryCoordinates GlobalEncoding LocalCoverBounds

variable {lim : Limits}



















private theorem leftMasks_eq {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : pre.length = k) (hk : k < J) :
    LightBlockChildren.leftMasks (leftPrefix k (prefixRows (J := J) pre))
        (blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩)) h =
      (childPrefixes q pre hk).map fun next => subsetMask (leftPrefix (k+1) (prefixRows (J := J) next)) := by
  simp only [LightBlockChildren.leftMasks,childPrefixes,localChildren,globalChildren,List.map_map]
  apply List.map_congr_left
  intro T hT
  have ht := (missingSets_mem _ _ _).mp hT
  simp only [Function.comp_apply]
  rw [prefixRows_append pre hp hk,leftPrefix_step,
    blockSet_localRow _ _ ht.1]

private theorem rightMasks_eq {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : pre.length = k) (hk : k < J) :
    LightBlockChildren.rightMasks (rightPrefix k (outputRows q) (prefixRows (J := J) pre))
        (blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩)) h =
      (childPrefixes q pre hk).map fun next =>
        subsetMask (rightPrefix (k+1) (outputRows q) (prefixRows (J := J) next)) := by
  simp only [LightBlockChildren.rightMasks,childPrefixes,localChildren,globalChildren,List.map_map]
  apply List.map_congr_left
  intro T hT
  have ht := (missingSets_mem _ _ _).mp hT
  have he : blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩ \ localRow ⟨k,hk⟩ T) =
      blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩) \ T := by
    have heT := blockSet_localRow ⟨k,hk⟩ (outputRows q ⟨k,hk⟩) ht.1
    conv_rhs => rw [← heT]
    ext x
    obtain ⟨⟨i,a⟩,rfl⟩ := (coordEquiv J (512*h)).surjective x
    simp only [mem_blockSet,Finset.mem_sdiff]
    tauto
  simp only [Function.comp_apply]
  rw [prefixRows_append pre hp hk,rightPrefix_step,he]
































theorem program_meets_sourceProof {μ : ℕ → ℤ} {h J k masks dstL dstR work d : ℕ}
    (q : GlobalOutput h J) (pre : List (Finset (Fin (512*h))))
    (hp : ValidPrefix q k pre) (hk : k < J)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hmasks : masks+groupSize h ≤ dstL)
    (hleft : dstL+groupSize h ≤ dstR)
    (hright : dstR+groupSize h ≤ work)
    (hspace : work+(2*(J*(512*h))+2) ≤ lim.space)
    (hword : ((2^(J*(512*h)+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+J*(512*h)+3 ≤ lim.depth) :
    Meets lim LightBlockChildren.program 0 d
      [J*(512*h),h,rowMask (outputRows q) ⟨k,hk⟩,
        subsetMask (leftPrefix k (prefixRows (J := J) pre)),
        subsetMask (rightPrefix k (outputRows q) (prefixRows (J := J) pre)),
        subsetMask (querySet k (outputRows q)),masks,dstL,dstR,work]
      μ (LightBlockChildren.time (J*(512*h)) (2*h) h)
      (fun r μ' =>
        r = (subsetMask (querySet (k+1) (outputRows q)) : ℤ) ∧
        SegN μ' masks ((globalChildren ⟨k,hk⟩ (outputRows q ⟨k,hk⟩) h).map subsetMask) ∧
        SegN μ' dstL ((childPrefixes q pre hk).map fun next =>
          subsetMask (leftPrefix (k+1) (prefixRows (J := J) next))) ∧
        SegN μ' dstR ((childPrefixes q pre hk).map fun next =>
          subsetMask (rightPrefix (k+1) (outputRows q) (prefixRows (J := J) next))) ∧
        Kept μ μ' masks) := by
  have hc : (blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩)).card = 2*h := by
    rw [blockSet_card]
    exact LayerCounts.mem_vertices.mp (q ⟨k,hk⟩).2.property
  have hcount : (blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩)).card.choose h = groupSize h := by
    rw [hc]
    rfl
  have hcall := LightBlockChildren.program_meets (μ := μ) (d := d)
    (leftPrefix k (prefixRows (J := J) pre))
    (rightPrefix k (outputRows q) (prefixRows (J := J) pre))
    (blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩)) (querySet k (outputRows q))
    hw (prefix_disjoint_block _ hk _) (prefix_disjoint_block _ hk _)
    (blockSet_subset_query _ hk) (by rw [hc]; omega)
    (hcount ▸ hmasks) (hcount ▸ hleft) (hcount ▸ hright) hspace hword hd
  have hrow : subsetMask (blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩)) = rowMask (outputRows q) ⟨k,hk⟩ := by
    simp [rowMask]
  rw [hrow,hc,leftMasks_eq q pre hp.1 hk,rightMasks_eq q pre hp.1 hk,
    ← querySet_step (outputRows q) hk] at hcall
  exact hcall









end ThreeSum.LightBlockChildrenIndexed

end


theorem solution : ∀ {lim : Light.Limits} {μ : Nat → Int} {h J k masks dstL dstR work d : Nat}
  (q : ThreeSum.GlobalEncoding.GlobalOutput h J)
  (pre :
    List.{0}
      (Finset.{0}
        (Fin
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))),
  @ThreeSum.StoredReporting.ValidPrefix h J q k pre →
    ∀ (hk : @LT.lt.{0} Nat instLTNat k J),
      @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word →
        @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) masks
              (ThreeSum.LocalCoverBounds.groupSize h))
            dstL →
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dstL
                (ThreeSum.LocalCoverBounds.groupSize h))
              dstR →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dstR
                  (ThreeSum.LocalCoverBounds.groupSize h))
                work →
              @LE.le.{0} Nat instLENat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  lim.space →
                @LE.le.{0} Int Int.instLEInt
                    (@Nat.cast.{0} Int instNatCastInt
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    lim.word →
                  @LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      lim.depth →
                    Light.Meets lim ThreeSum.LightBlockChildren.program
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d
                      (@List.cons.{0} Int
                        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                          (@Nat.cast.{0} Int instNatCastInt J)
                          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                            (@OfNat.ofNat.{0} Int (nat_lit 512) (@instOfNat (nat_lit 512)))
                            (@Nat.cast.{0} Int instNatCastInt h)))
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h)
                          (@List.cons.{0} Int
                            (@Nat.cast.{0} Int instNatCastInt
                              (@ThreeSum.BlockMaskLayout.rowMask J
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                (@ThreeSum.BlockForced.outputRows h J q) (@Fin.mk J k hk)))
                            (@List.cons.{0} Int
                              (@Nat.cast.{0} Int instNatCastInt
                                (@ThreeSum.SubsetAddress.subsetMask
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                                  (@ThreeSum.BlockIndexedQuery.leftPrefix J
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                    k
                                    (@ThreeSum.StoredReporting.prefixRows J
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                      pre))))
                              (@List.cons.{0} Int
                                (@Nat.cast.{0} Int instNatCastInt
                                  (@ThreeSum.SubsetAddress.subsetMask
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                                    (@ThreeSum.BlockIndexedQuery.rightPrefix J
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                      k (@ThreeSum.BlockForced.outputRows h J q)
                                      (@ThreeSum.StoredReporting.prefixRows J
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                        pre))))
                                (@List.cons.{0} Int
                                  (@Nat.cast.{0} Int instNatCastInt
                                    (@ThreeSum.SubsetAddress.subsetMask
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                                      (@ThreeSum.BlockIndexedQuery.querySet J
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                        k (@ThreeSum.BlockForced.outputRows h J q))))
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt masks)
                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dstL)
                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dstR)
                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                          (@List.nil.{0} Int)))))))))))
                      μ
                      (ThreeSum.LightBlockChildren.time
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
                        h)
                      fun (r : Int) (μ' : Nat → Int) =>
                      And
                        (@Eq.{1} Int r
                          (@Nat.cast.{0} Int instNatCastInt
                            (@ThreeSum.SubsetAddress.subsetMask
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                              (@ThreeSum.BlockIndexedQuery.querySet J
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (@ThreeSum.BlockForced.outputRows h J q)))))
                        (And
                          (Light.SegN μ' masks
                            (@List.map.{0, 0}
                              (Finset.{0}
                                (Fin
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
                              Nat
                              (@ThreeSum.SubsetAddress.subsetMask
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
                              (@ThreeSum.ReportingHostMasks.globalChildren J
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                (@Fin.mk J k hk) (@ThreeSum.BlockForced.outputRows h J q (@Fin.mk J k hk)) h)))
                          (And
                            (Light.SegN μ' dstL
                              (@List.map.{0, 0}
                                (List.{0}
                                  (Finset.{0}
                                    (Fin
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
                                Nat
                                (fun
                                    (next :
                                      List.{0}
                                        (Finset.{0}
                                          (Fin
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))) =>
                                  @ThreeSum.SubsetAddress.subsetMask
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                                    (@ThreeSum.BlockIndexedQuery.leftPrefix J
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                      (@ThreeSum.StoredReporting.prefixRows J
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                        next)))
                                (@ThreeSum.LightBlockChildrenIndexed.childPrefixes h J k q pre hk)))
                            (And
                              (Light.SegN μ' dstR
                                (@List.map.{0, 0}
                                  (List.{0}
                                    (Finset.{0}
                                      (Fin
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
                                  Nat
                                  (fun
                                      (next :
                                        List.{0}
                                          (Finset.{0}
                                            (Fin
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512)))
                                                h)))) =>
                                    @ThreeSum.SubsetAddress.subsetMask
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                                      (@ThreeSum.BlockIndexedQuery.rightPrefix J
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                        (@ThreeSum.BlockForced.outputRows h J q)
                                        (@ThreeSum.StoredReporting.prefixRows J
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                                          next)))
                                  (@ThreeSum.LightBlockChildrenIndexed.childPrefixes h J k q pre hk)))
                              (Light.Kept μ μ' masks)))) := by
  exact @ThreeSum.LightBlockChildrenIndexed.program_meets_sourceProof

#print axioms solution
