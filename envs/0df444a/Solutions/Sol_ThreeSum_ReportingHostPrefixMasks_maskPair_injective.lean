-- Prove2me | solution 1 for ThreeSum.ReportingHostPrefixMasks.maskPair_injective
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:52:59.970218+00:00
-- url     : https://prove2.me/submissions/eb465ab5-f204-41ea-bb0f-babbddcc7d41

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
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
import Mathlib.Data.List.TakeDrop
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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
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
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.ReportingHostPairEnumeration
end ThreeSum.ReportingHostPairEnumeration
namespace ThreeSum.ReportingHostPrefixCatalog
end ThreeSum.ReportingHostPrefixCatalog
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















@[simp] theorem row_join {J L : ℕ} (I : Finset (Fin J))
    (u : Fin J → Finset (Fin L)) (i : Fin J) :
    row (join I u) i = if i ∈ I then u i else ∅ := by
  ext x
  by_cases hi : i ∈ I <;> simp [hi]





























































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





















@[simp] theorem unindex_index {J L : ℕ} (S : Finset (Coord J L)) :
    unindexSet (indexSet S) = S := by
  ext c
  simp [unindexSet,indexSet]





























































































end ThreeSum.BlockIndex

end

section


/-!
# Positional products are the physical masks of the complete shared prefix catalog

Both left and right products use one common tuple list. Every original valid
prefix has a key in that list, and the tuple encodes exactly its original
row-major global masks.
-/

namespace ThreeSum.ReportingHostPrefixMasks

open Finset ThreeSum.SubsetAddress BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open BlockForced
open ReportingHostPrefixCatalog ReportingHostPairEnumeration
open scoped BigOperators

set_option maxHeartbeats 500000

variable {α : Type*}


































































































theorem maskPair_injective_sourceProof {h J k : ℕ} (hk : k ≤ J) :
    Function.Injective (fun p : Prefix h k =>
      (subsetMask (leftSet (J := J) p),subsetMask (rightSet (J := J) p))) := by
  intro p q he
  have hL := subsetMask_injective (J*(512*h)) (congrArg Prod.fst he)
  have hR := subsetMask_injective (J*(512*h)) (congrArg Prod.snd he)
  funext i
  apply Subtype.ext
  apply Prod.ext
  · have hh := congrArg (fun S => row (unindexSet S) (⟨i.val,i.isLt.trans_le hk⟩ : Fin J)) hL
    simpa only [leftSet,leftPrefix,unindex_index,prefixLeft,row_join,mem_prefixIndices,
      dif_pos i.isLt,leftRows,i.isLt,ite_true,dite_true] using hh
  · have hh := congrArg (fun S => row (unindexSet S) (⟨i.val,i.isLt.trans_le hk⟩ : Fin J)) hR
    simpa only [rightSet,leftPrefix,unindex_index,prefixLeft,row_join,mem_prefixIndices,
      dif_pos i.isLt,rightRows,i.isLt,ite_true,dite_true] using hh

end ThreeSum.ReportingHostPrefixMasks

end


theorem solution : ∀ {h J k : Nat},
  @LE.le.{0} Nat instLENat k J →
    @Function.Injective.{1, 1} (ThreeSum.ReportingHostPrefixCatalog.Prefix h k) (Prod.{0, 0} Nat Nat)
      fun (p : ThreeSum.ReportingHostPrefixCatalog.Prefix h k) =>
      @Prod.mk.{0, 0} Nat Nat
        (@ThreeSum.SubsetAddress.subsetMask
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
          (@ThreeSum.ReportingHostPrefixCatalog.leftSet h J k p))
        (@ThreeSum.SubsetAddress.subsetMask
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
          (@ThreeSum.ReportingHostPrefixCatalog.rightSet h J k p)) := by
  exact @ThreeSum.ReportingHostPrefixMasks.maskPair_injective_sourceProof

#print axioms solution
