-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixValueBounds.prefix_count_le_word
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:32:44.449525+00:00
-- url     : https://prove2.me/submissions/f5d0a237-0ba5-45c4-9caa-48ca0e26ad80

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
import Definitions.Def_ThreeSum1960614_Machine_Bundle026
import Definitions.Def_ThreeSum1960614_Machine_Bundle027
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Lean
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_StoredReporting_storedQueryValue_eq_prefixQuery
import Theorems.Thm_ThreeSum_BlockIndexedQuery_index_suffixDomain
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_abs_le

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingSuffixBoxes
end ThreeSum.LightReportingSuffixBoxes
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.ReportingHostSuffixValueBounds
end ThreeSum.ReportingHostSuffixValueBounds
namespace ThreeSum.SignedLeaf
end ThreeSum.SignedLeaf
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.SubsetTransport
end ThreeSum.SubsetTransport
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBoxes
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBoxes
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixValueBounds
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixValueBounds
namespace ThreeSum1960614.Machine.ThreeSum.SignedLeaf
end ThreeSum1960614.Machine.ThreeSum.SignedLeaf
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.SubsetTransport
end ThreeSum1960614.Machine.ThreeSum.SubsetTransport

namespace ThreeSum1960614.Machine

/-!
# Flattening a block family of subsets

The coordinates retain the block index explicitly. Joining and slicing are
mutually inverse, preserve Boolean set operations, and give exact cardinalities
for balanced full inputs and forced prefixes.
-/

namespace ThreeSum.BlockRows
open _root_.ThreeSum.BlockRows


open _root_.Finset
open scoped _root_.BigOperators









@[simp] theorem mem_join {J L : ℕ} {I : Finset (Fin J)}
    {u : Fin J → Finset (Fin L)} {i : Fin J} {x : Fin L} :
    Sigma.mk i x ∈ _root_.ThreeSum.BlockRows.join I u ↔ i ∈ I ∧ x ∈ u i := Finset.mem_sigma























theorem join_disjoint_compl {J L : ℕ} (I : Finset (Fin J))
    (u v : Fin J → Finset (Fin L)) : Disjoint (_root_.ThreeSum.BlockRows.join I u) (_root_.ThreeSum.BlockRows.join Iᶜ v) := by
  apply Finset.disjoint_left.mpr
  intro ⟨i, x⟩ hx hy
  exact (Finset.mem_compl.mp (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join.mp hy).1) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join.mp hx).1



theorem join_card {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    (_root_.ThreeSum.BlockRows.join I u).card = ∑ i ∈ I, (u i).card := Finset.card_sigma _ _

theorem join_card_of_balance {J L h : ℕ} (I : Finset (Fin J))
    (u : Fin J → Finset (Fin L)) (hu : ∀ i ∈ I, (u i).card = h) :
    (_root_.ThreeSum.BlockRows.join I u).card = I.card * h := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card]
  simp only [Finset.sum_congr rfl hu, Finset.sum_const, Nat.nsmul_eq_mul]







@[simp] theorem mem_prefixIndices {J k : ℕ} {i : Fin J} :
    i ∈ _root_.ThreeSum.BlockRows.prefixIndices J k ↔ i.val < k := by simp [_root_.ThreeSum.BlockRows.prefixIndices]



end ThreeSum.BlockRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Signed leaf weights and the explicit part of sparse queries

The alternating sign is separated from the query cardinality, allowing
the same leaf weights to be used in stored boxes and direct leaf reads.
-/

namespace ThreeSum.SignedLeaf
open _root_.ThreeSum.SignedLeaf


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators





theorem abs_value_le {W cut B C : ℕ} (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (preL preR S : Finset (Fin W))
    (hstage : stage ≤ W) (hL : (preL ∪ S).card ≤ cut) (hR : (preR ∪ S).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ C) :
    |_root_.ThreeSum.SignedLeaf.value f g stage preL preR S| ≤ (((2^stage*B)*(2^stage*C) : ℕ) : ℤ) := by
  rw [_root_.ThreeSum.SignedLeaf.value,abs_mul,abs_neg_one_pow,one_mul,abs_mul]
  have h₁ := _root_.ThreeSum.SubsetStages.stageValue_abs_le f hf stage hstage (preL ∪ S) hL
  have h₂ := _root_.ThreeSum.SubsetStages.stageValue_abs_le g hg stage hstage (preR ∪ S) hR
  simpa only [Nat.cast_mul] using mul_le_mul h₁ h₂ (abs_nonneg _) (Int.natCast_nonneg _)

theorem neg_one_pow_sub {a b : ℕ} (h : b ≤ a) :
    (-1 : ℤ)^(a-b) = (-1 : ℤ)^a*(-1 : ℤ)^b := by
  have ha : a = (a-b)+b := by omega
  rw [ha,pow_add,mul_assoc,← pow_add]
  have hb : b+b = 2*b := by omega
  rw [hb,pow_mul]
  norm_num

theorem mobius_eq_signed_sum {W : ℕ} (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (preL preR Q : Finset (Fin W)) :
    _root_.ThreeSum.Subset.mobius
      (fun S => _root_.ThreeSum.SubsetStages.stageValue f stage (preL ∪ S)*
        _root_.ThreeSum.SubsetStages.stageValue g stage (preR ∪ S)) Q =
      (-1 : ℤ)^Q.card * ∑ S ∈ Q.powerset, _root_.ThreeSum.SignedLeaf.value f g stage preL preR S := by
  rw [_root_.ThreeSum.Subset.mobius,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SignedLeaf.neg_one_pow_sub (Finset.card_le_card (Finset.mem_powerset.mp hS)),_root_.ThreeSum.SignedLeaf.value]
  ring













end ThreeSum.SignedLeaf

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Transporting compact subset transforms across an explicit equivalence -/

namespace ThreeSum.SubsetTransport
open _root_.ThreeSum.SubsetTransport


open _root_.Finset
open scoped _root_.BigOperators

variable {α β : Type*} [DecidableEq α] [DecidableEq β]



@[simp] theorem reindex_map (e : α ≃ β) (f : Finset α → ℤ) (S : Finset α) :
    _root_.ThreeSum.SubsetTransport.reindex e f (S.map e.toEmbedding) = f S := by
  unfold _root_.ThreeSum.SubsetTransport.reindex
  congr 1
  ext a
  simp

theorem sum_powerset_map (e : α ≃ β) (S : Finset α) (f : Finset β → ℤ) :
    (∑ T ∈ (S.map e.toEmbedding).powerset, f T) =
      ∑ T ∈ S.powerset, f (T.map e.toEmbedding) := by
  simp only [Finset.map_eq_image]
  rw [Finset.powerset_image,Finset.sum_image]
  intro A hA B hB he
  exact (Finset.image_inj e.injective).mp he





theorem partialZeta_map (e : α ≃ β) (f : Finset α → ℤ) (processed S : Finset α) :
    _root_.ThreeSum.Subset.partialZeta (processed.map e.toEmbedding) (_root_.ThreeSum.SubsetTransport.reindex e f) (S.map e.toEmbedding) =
      _root_.ThreeSum.Subset.partialZeta processed f S := by
  unfold _root_.ThreeSum.Subset.partialZeta
  rw [← Finset.map_inter,_root_.ThreeSum1960614.Machine.ThreeSum.SubsetTransport.sum_powerset_map]
  apply Finset.sum_congr rfl
  intro T hT
  rw [← Finset.map_sdiff,← Finset.map_union,_root_.ThreeSum1960614.Machine.ThreeSum.SubsetTransport.reindex_map]

theorem mobius_partial_product_map (e : α ≃ β) (f g : Finset α → ℤ)
    (processed preL preR Q : Finset α) :
    _root_.ThreeSum.Subset.mobius (fun S =>
      _root_.ThreeSum.Subset.partialZeta (processed.map e.toEmbedding) (_root_.ThreeSum.SubsetTransport.reindex e f) (preL.map e.toEmbedding ∪ S) *
      _root_.ThreeSum.Subset.partialZeta (processed.map e.toEmbedding) (_root_.ThreeSum.SubsetTransport.reindex e g) (preR.map e.toEmbedding ∪ S))
      (Q.map e.toEmbedding) =
      _root_.ThreeSum.Subset.mobius (fun S => _root_.ThreeSum.Subset.partialZeta processed f (preL ∪ S) *
        _root_.ThreeSum.Subset.partialZeta processed g (preR ∪ S)) Q := by
  unfold _root_.ThreeSum.Subset.mobius
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetTransport.sum_powerset_map]
  simp only [← Finset.map_union,_root_.ThreeSum1960614.Machine.ThreeSum.SubsetTransport.partialZeta_map,Finset.card_map]

end ThreeSum.SubsetTransport

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Explicit row-major encoding of the block ground set

Block coordinates are numbered by `block * width + coordinate`. The
equivalence connects compact machine-mask tables on `Fin (J*L)` with the
sigma-typed block sets in the reporting proof. Flattened one-hot coefficients
already include their positional radix factors.
-/

namespace ThreeSum.BlockIndex
open _root_.ThreeSum.BlockIndex


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open scoped _root_.BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false











@[simp] theorem indexSet_card {J L : ℕ} (S : Finset (_root_.ThreeSum.BlockRows.Coord J L)) :
    (_root_.ThreeSum.BlockIndex.indexSet S).card = S.card := Finset.card_map _























end ThreeSum.BlockIndex

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact bridge from row-major machine masks to the block reporting query

The explicit coordinate equivalence sends the remaining blocks to a
contiguous suffix. Transport of finite subset sums identifies the machine's
Möbius value with the concrete forced-prefix count used by reporting.
-/

namespace ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockIndexedQuery


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open scoped _root_.BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

@[simp] theorem prefixIndices_card {J k : ℕ} (hk : k ≤ J) :
    (_root_.ThreeSum.BlockRows.prefixIndices J k).card = k := by
  simpa only [_root_.ThreeSum.BlockRows.prefixIndices,Nat.min_eq_right hk] using (Fin.card_filter_val_lt (n := J) (m := k))



theorem suffixStage_le (J L k : ℕ) : _root_.ThreeSum.BlockIndexedQuery.suffixStage J L k ≤ J*L :=
  Nat.mul_le_mul_right L (Nat.sub_le _ _)









theorem leftPrefix_disjoint_query {J L : ℕ} (k : ℕ) (Q u : Fin J → Finset (Fin L)) :
    Disjoint (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k u) (_root_.ThreeSum.BlockIndexedQuery.querySet k Q) := by
  exact (Finset.disjoint_map _).mpr (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_disjoint_compl (_root_.ThreeSum.BlockRows.prefixIndices J k) u Q)

theorem rightPrefix_disjoint_query {J L : ℕ} (k : ℕ) (Q u : Fin J → Finset (Fin L)) :
    Disjoint (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k Q u) (_root_.ThreeSum.BlockIndexedQuery.querySet k Q) := by
  exact (Finset.disjoint_map _).mpr
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_disjoint_compl (_root_.ThreeSum.BlockRows.prefixIndices J k) (fun i => Q i \ u i) Q)



theorem leftPrefix_card {J L h k : ℕ} (hk : k ≤ J) (u : Fin J → Finset (Fin L))
    (hu : ∀ i ∈ _root_.ThreeSum.BlockRows.prefixIndices J k, (u i).card = h) : (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k u).card = k*h := by
  rw [_root_.ThreeSum.BlockIndexedQuery.leftPrefix,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.indexSet_card,_root_.ThreeSum.BlockForced.prefixLeft,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card_of_balance _ _ hu,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.prefixIndices_card hk]

theorem rightPrefix_card {J L h k : ℕ} (hk : k ≤ J) (Q u : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h)
    (hu : ∀ i ∈ _root_.ThreeSum.BlockRows.prefixIndices J k, u i ⊆ Q i ∧ (u i).card = h) :
    (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k Q u).card = k*h := by
  have hc : ∀ i ∈ _root_.ThreeSum.BlockRows.prefixIndices J k, (Q i \ u i).card = h := by
    intro i hi
    rw [Finset.card_sdiff_of_subset (hu i hi).1,hQ i,(hu i hi).2]
    omega
  rw [_root_.ThreeSum.BlockIndexedQuery.rightPrefix,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.indexSet_card,_root_.ThreeSum.BlockForced.prefixRight,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card_of_balance _ _ hc,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.prefixIndices_card hk]

theorem querySet_card {J L h k : ℕ} (hk : k ≤ J) (Q : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h) : (_root_.ThreeSum.BlockIndexedQuery.querySet k Q).card = (J-k)*(2*h) := by
  rw [_root_.ThreeSum.BlockIndexedQuery.querySet,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.indexSet_card,_root_.ThreeSum.BlockForced.remaining,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card_of_balance _ _ (fun i _ => hQ i),
    Finset.card_compl,Fintype.card_fin,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.prefixIndices_card hk]

section

private theorem private_c26fa15725_sizes_le {J h k : ℕ} (hk : k ≤ J) : k*h+(J-k)*(2*h) ≤ 2*h*J := by
  calc
    _ ≤ k*(2*h)+(J-k)*(2*h) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left k (by omega)) _
    _ = (k+(J-k))*(2*h) := (Nat.add_mul _ _ _).symm
    _ = _ := by rw [Nat.add_sub_of_le hk]; ring
end


theorem left_union_card_le {J L h k : ℕ} (hk : k ≤ J) (Q u : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h)
    (hu : ∀ i ∈ _root_.ThreeSum.BlockRows.prefixIndices J k, (u i).card = h) :
    (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k u ∪ _root_.ThreeSum.BlockIndexedQuery.querySet k Q).card ≤ 2*h*J := by
  rw [Finset.card_union_of_disjoint (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftPrefix_disjoint_query k Q u),
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftPrefix_card hk u hu,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.querySet_card hk Q hQ]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.private_c26fa15725_sizes_le hk

theorem right_union_card_le {J L h k : ℕ} (hk : k ≤ J) (Q u : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h)
    (hu : ∀ i ∈ _root_.ThreeSum.BlockRows.prefixIndices J k, u i ⊆ Q i ∧ (u i).card = h) :
    (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k Q u ∪ _root_.ThreeSum.BlockIndexedQuery.querySet k Q).card ≤ 2*h*J := by
  rw [Finset.card_union_of_disjoint (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightPrefix_disjoint_query k Q u),
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightPrefix_card hk Q u hQ hu,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.querySet_card hk Q hQ]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.private_c26fa15725_sizes_le hk

section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]





theorem leftWeights_le_card {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (P : ℤ)
    (B : Finset β) (b : β → ℤ) (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights o P B b S ≤ B.card := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights
  split_ifs with ha
  · calc
      _ ≤ ∑ _j ∈ B, (1 : ℕ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
      _ = _ := by simp
  · omega

theorem rightWeights_le_card {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (P d : ℤ)
    (C : Finset γ) (c : γ → ℤ) (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights o P d C c S ≤ C.card := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights
  split_ifs with ha
  · calc
      _ ≤ ∑ _j ∈ C, (1 : ℕ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
      _ = _ := by simp
  · omega

theorem leftSource_abs_le {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ)
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (S : Finset (Fin (J*(464*h)))) : |_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource P B b q S| ≤ B.card := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource _root_.ThreeSum.SubsetTransport.reindex
  rw [Int.abs_natCast]
  exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftWeights_le_card (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P B b _

theorem rightSource_abs_le {h J : ℕ} (P d : ℤ) (C : Finset γ) (c : γ → ℤ)
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (S : Finset (Fin (J*(464*h)))) : |_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource P d C c q S| ≤ C.card := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource _root_.ThreeSum.SubsetTransport.reindex
  rw [Int.abs_natCast]
  exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightWeights_le_card (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P d C c _



theorem queryValue_eq_transformPrefixValue {h J k : ℕ} (P d : ℤ)
    (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (u : Fin J → Finset (Fin (464*h))) (hk : k ≤ J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.queryValue P d B C b c q k u =
      _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.transformPrefixValue P d B C b c q (_root_.ThreeSum.BlockRows.prefixIndices J k) u := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.queryValue _root_.ThreeSum.SubsetStages.stageValue
  rw [← _root_.ThreeSum.BlockIndexedQuery.index_suffixDomain hk]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SubsetTransport.mobius_partial_product_map (_root_.ThreeSum.BlockIndex.coordEquiv J (464*h)) _ _ _ _ _ _



end Histograms

end ThreeSum.BlockIndexedQuery

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The actual sparse-query machine returns the original raw prefix mass

All coordinate transport, prefix sizes, source bounds, and cutoff facts
are discharged for the concrete block histograms. The remaining storage
premises are precisely the arrays produced by source and box preprocessing.
-/

namespace ThreeSum.LightBlockQuery
open _root_.ThreeSum.LightBlockQuery


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}







section OriginalIndices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem queryValue_eq_prefixQuery {h J k : ℕ} (pMod shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (pre : List (Finset (Fin (464*h)))) (hk : k ≤ J) (hp : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣
      (a w.1 % pMod + _root_.ThreeSum.RawIncidences.lift w.2.1*pMod + shift)-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.queryValue pMod shift B C b c w.2.2 k (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre) =
      ((_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℕ) : ℤ) := by
  calc
    _ = _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.transformPrefixValue pMod shift B C b c w.2.2 (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre) :=
      _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.queryValue_eq_transformPrefixValue pMod shift B C b c w.2.2 (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre) hk
    _ = _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.storedQueryValue pMod shift A B C a b c w k pre := by
      simp [_root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.storedQueryValue,hp,hkey]
    _ = _ := _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.storedQueryValue_eq_prefixQuery pMod shift A B C a b c w pre hk





end OriginalIndices

end ThreeSum.LightBlockQuery

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual shrinking-suffix box preprocessing for an original valid block prefix -/

namespace ThreeSum.LightReportingSuffixBoxes
open _root_.ThreeSum.LightReportingSuffixBoxes


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]



theorem residual_le_suffix {h J k : ℕ} : _root_.ThreeSum.LightBlockQuery.residualSize h J k ≤ _root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k := by
  exact Nat.mul_le_mul_left (J-k) (by omega)



end ThreeSum.LightReportingSuffixBoxes

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Original prefix counts fit the shrinking-suffix query word bound -/

namespace ThreeSum.ReportingHostSuffixValueBounds
open _root_.ThreeSum.ReportingHostSuffixValueBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open scoped _root_.BigOperators

theorem abs_value_le_card {W cut stage B D : ℕ} (f g : Finset (Fin W) → ℤ)
    (preL preR Q : Finset (Fin W)) (hstage : stage ≤ W)
    (hL : (preL ∪ Q).card ≤ cut) (hR : (preR ∪ Q).card ≤ cut)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ B)
    (hg : ∀ S, S.card ≤ cut → |g S| ≤ D) :
    |_root_.ThreeSum.ReportingHostQueryBounds.value f g stage preL preR Q| ≤
      ((2^Q.card*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) := by
  unfold _root_.ThreeSum.ReportingHostQueryBounds.value
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SignedLeaf.mobius_eq_signed_sum,abs_mul,abs_neg_one_pow,one_mul]
  calc
    _ ≤ ∑ S ∈ Q.powerset, |_root_.ThreeSum.SignedLeaf.value f g stage preL preR S| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S ∈ Q.powerset, (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) := by
      apply Finset.sum_le_sum
      intro S hS
      have hs := Finset.mem_powerset.mp hS
      exact _root_.ThreeSum1960614.Machine.ThreeSum.SignedLeaf.abs_value_le f g stage preL preR S hstage
        ((Finset.card_le_card (Finset.union_subset_union (le_refl preL) hs)).trans hL)
        ((Finset.card_le_card (Finset.union_subset_union (le_refl preR) hs)).trans hR) hf hg
    _ = _ := by simp [Nat.cast_mul]

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]



end ThreeSum.ReportingHostSuffixValueBounds

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixValueBounds

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open scoped _root_.BigOperators
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
section

theorem ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixValueBounds.prefix_count_le_word__implementation_2c3618d4d9 {h J k t : ℕ}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (pre : List (Finset (Fin (464*h)))) (hk : k ≤ J) (hp : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣
      (a w.1 % pMod+_root_.ThreeSum.RawIncidences.lift w.2.1*pMod+shift)-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2)
    (hvalueWord : (_root_.ThreeSum.LightSparseQuery.magnitudeBound (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k)
      (_root_.ThreeSum.LightBlockQuery.residualSize h J k) t B.card C.card : ℤ) ≤ lim.word) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℤ) ≤ lim.word := by
  have hQ : ∀ i, (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2 i).card = 2*h :=
    fun i => _root_.ThreeSum.LayerCounts.mem_vertices.mp (w.2.2 i).2.property
  have hprefix : ∀ j ∈ _root_.ThreeSum.BlockRows.prefixIndices J k,
      _root_.ThreeSum.StoredReporting.prefixRows (J := J) pre j ⊆ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2 j ∧ (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre j).card = h := by
    intro j hj
    exact hp.2 j (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_prefixIndices.mp hj)
  have hQc : (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2)).card = _root_.ThreeSum.LightBlockQuery.residualSize h J k := _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.querySet_card hk _ hQ
  have hv := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixValueBounds.abs_value_le_card
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource pMod B b w.2.2) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource pMod shift C c w.2.2)
    (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre))
    (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre))
    (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2)) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.suffixStage_le J (464*h) k)
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.left_union_card_le hk _ _ hQ (fun j hj => (hprefix j hj).2))
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.right_union_card_le hk _ _ hQ hprefix)
    (fun S _ => _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource_abs_le pMod B b w.2.2 S)
    (fun S _ => _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource_abs_le pMod shift C c w.2.2 S)
  change |_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.queryValue pMod shift B C b c w.2.2 k (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre)| ≤ _ at hv
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.queryValue_eq_prefixQuery pMod shift A B C a b c w pre hk hp hkey,Int.abs_natCast,hQc] at hv
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ))
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBoxes.residual_le_suffix (h := h) (J := J) (k := k))
  have hmul := Nat.mul_le_mul_right
    ((2^(_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k)*B.card)*(2^(_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k)*C.card)) hpow
  have hm : 2^(_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k)*
      ((2^(_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k)*B.card)*(2^(_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k)*C.card)) ≤
      _root_.ThreeSum.LightSparseQuery.magnitudeBound (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k)
        (_root_.ThreeSum.LightBlockQuery.residualSize h J k) t B.card C.card := Nat.le_mul_of_pos_left _ (by omega)
  exact hv.trans ((Int.ofNat_le.mpr (hmul.trans hm)).trans hvalueWord)
end

end

theorem solution.{u_implementation_0,u_implementation_1,u_implementation_2} : type_of% (@ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixValueBounds.prefix_count_le_word__implementation_2c3618d4d9.{u_implementation_0,u_implementation_1,u_implementation_2}) := (@ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixValueBounds.prefix_count_le_word__implementation_2c3618d4d9.{u_implementation_0,u_implementation_1,u_implementation_2})

#print axioms solution
