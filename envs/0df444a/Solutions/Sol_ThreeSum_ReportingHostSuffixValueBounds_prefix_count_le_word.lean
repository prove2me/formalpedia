-- Prove2me | solution 1 for ThreeSum.ReportingHostSuffixValueBounds.prefix_count_le_word
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:18:49.063708+00:00
-- url     : https://prove2.me/submissions/5d85cff4-50d3-4a04-9dae-bf400720a907

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
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
import Theorems.Thm_ThreeSum_BlockIndexedQuery_index_suffixDomain
import Theorems.Thm_ThreeSum_StoredReporting_storedQueryValue_eq_prefixQuery
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_abs_le


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
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
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
















































theorem join_disjoint_compl {J L : ℕ} (I : Finset (Fin J))
    (u v : Fin J → Finset (Fin L)) : Disjoint (join I u) (join Iᶜ v) := by
  apply Finset.disjoint_left.mpr
  intro ⟨i, x⟩ hx hy
  exact (Finset.mem_compl.mp (mem_join.mp hy).1) (mem_join.mp hx).1







theorem join_card {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    (join I u).card = ∑ i ∈ I, (u i).card := Finset.card_sigma _ _

theorem join_card_of_balance {J L h : ℕ} (I : Finset (Fin J))
    (u : Fin J → Finset (Fin L)) (hu : ∀ i ∈ I, (u i).card = h) :
    (join I u).card = I.card * h := by
  rw [join_card]
  simp only [Finset.sum_congr rfl hu, Finset.sum_const, Nat.nsmul_eq_mul]













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


















@[simp] theorem indexSet_card {J L : ℕ} (S : Finset (Coord J L)) :
    (indexSet S).card = S.card := Finset.card_map _


































































































end ThreeSum.BlockIndex

end

section


/-! # Transporting compact subset transforms across an explicit equivalence -/

namespace ThreeSum.SubsetTransport

open Finset
open scoped BigOperators

variable {α β : Type*} [DecidableEq α] [DecidableEq β]




@[simp] theorem reindex_map (e : α ≃ β) (f : Finset α → ℤ) (S : Finset α) :
    reindex e f (S.map e.toEmbedding) = f S := by
  unfold reindex
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
    Subset.partialZeta (processed.map e.toEmbedding) (reindex e f) (S.map e.toEmbedding) =
      Subset.partialZeta processed f S := by
  unfold Subset.partialZeta
  rw [← Finset.map_inter,sum_powerset_map]
  apply Finset.sum_congr rfl
  intro T hT
  rw [← Finset.map_sdiff,← Finset.map_union,reindex_map]

theorem mobius_partial_product_map (e : α ≃ β) (f g : Finset α → ℤ)
    (processed preL preR Q : Finset α) :
    Subset.mobius (fun S =>
      Subset.partialZeta (processed.map e.toEmbedding) (reindex e f) (preL.map e.toEmbedding ∪ S) *
      Subset.partialZeta (processed.map e.toEmbedding) (reindex e g) (preR.map e.toEmbedding ∪ S))
      (Q.map e.toEmbedding) =
      Subset.mobius (fun S => Subset.partialZeta processed f (preL ∪ S) *
        Subset.partialZeta processed g (preR ∪ S)) Q := by
  unfold Subset.mobius
  rw [sum_powerset_map]
  simp only [← Finset.map_union,partialZeta_map,Finset.card_map]

end ThreeSum.SubsetTransport

end

section


/-!
# Exact bridge from row-major machine masks to the block reporting query

The explicit coordinate equivalence sends the remaining blocks to a
contiguous suffix. Transport of finite subset sums identifies the machine's
Möbius value with the concrete forced-prefix count used by reporting.
-/

namespace ThreeSum.BlockIndexedQuery

open Finset BlockRows BlockIndex BlockForced BlockEncoding GlobalEncoding
open LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open scoped BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

@[simp] theorem prefixIndices_card {J k : ℕ} (hk : k ≤ J) :
    (prefixIndices J k).card = k := by
  simpa only [prefixIndices,Nat.min_eq_right hk] using (Fin.card_filter_val_lt (n := J) (m := k))



theorem suffixStage_le (J L k : ℕ) : suffixStage J L k ≤ J*L :=
  Nat.mul_le_mul_right L (Nat.sub_le _ _)






























theorem leftPrefix_disjoint_query {J L : ℕ} (k : ℕ) (Q u : Fin J → Finset (Fin L)) :
    Disjoint (leftPrefix k u) (querySet k Q) := by
  exact (Finset.disjoint_map _).mpr (join_disjoint_compl (prefixIndices J k) u Q)

theorem rightPrefix_disjoint_query {J L : ℕ} (k : ℕ) (Q u : Fin J → Finset (Fin L)) :
    Disjoint (rightPrefix k Q u) (querySet k Q) := by
  exact (Finset.disjoint_map _).mpr
    (join_disjoint_compl (prefixIndices J k) (fun i => Q i \ u i) Q)






theorem leftPrefix_card {J L h k : ℕ} (hk : k ≤ J) (u : Fin J → Finset (Fin L))
    (hu : ∀ i ∈ prefixIndices J k, (u i).card = h) : (leftPrefix k u).card = k*h := by
  rw [leftPrefix,indexSet_card,prefixLeft,join_card_of_balance _ _ hu,prefixIndices_card hk]

theorem rightPrefix_card {J L h k : ℕ} (hk : k ≤ J) (Q u : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h)
    (hu : ∀ i ∈ prefixIndices J k, u i ⊆ Q i ∧ (u i).card = h) :
    (rightPrefix k Q u).card = k*h := by
  have hc : ∀ i ∈ prefixIndices J k, (Q i \ u i).card = h := by
    intro i hi
    rw [Finset.card_sdiff_of_subset (hu i hi).1,hQ i,(hu i hi).2]
    omega
  rw [rightPrefix,indexSet_card,prefixRight,join_card_of_balance _ _ hc,prefixIndices_card hk]

theorem querySet_card {J L h k : ℕ} (hk : k ≤ J) (Q : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h) : (querySet k Q).card = (J-k)*(2*h) := by
  rw [querySet,indexSet_card,remaining,join_card_of_balance _ _ (fun i _ => hQ i),
    Finset.card_compl,Fintype.card_fin,prefixIndices_card hk]

private theorem sizes_le {J h k : ℕ} (hk : k ≤ J) : k*h+(J-k)*(2*h) ≤ 2*h*J := by
  calc
    _ ≤ k*(2*h)+(J-k)*(2*h) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left k (by omega)) _
    _ = (k+(J-k))*(2*h) := (Nat.add_mul _ _ _).symm
    _ = _ := by rw [Nat.add_sub_of_le hk]; ring

theorem left_union_card_le {J L h k : ℕ} (hk : k ≤ J) (Q u : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h)
    (hu : ∀ i ∈ prefixIndices J k, (u i).card = h) :
    (leftPrefix k u ∪ querySet k Q).card ≤ 2*h*J := by
  rw [Finset.card_union_of_disjoint (leftPrefix_disjoint_query k Q u),
    leftPrefix_card hk u hu,querySet_card hk Q hQ]
  exact sizes_le hk

theorem right_union_card_le {J L h k : ℕ} (hk : k ≤ J) (Q u : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h)
    (hu : ∀ i ∈ prefixIndices J k, u i ⊆ Q i ∧ (u i).card = h) :
    (rightPrefix k Q u ∪ querySet k Q).card ≤ 2*h*J := by
  rw [Finset.card_union_of_disjoint (rightPrefix_disjoint_query k Q u),
    rightPrefix_card hk Q u hQ hu,querySet_card hk Q hQ]
  exact sizes_le hk

section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]











theorem leftWeights_le_card {h J : ℕ} (o : Occurrences h J) (P : ℤ)
    (B : Finset β) (b : β → ℤ) (S : Finset (Coord J (512*h))) :
    leftWeights o P B b S ≤ B.card := by
  unfold leftWeights
  split_ifs with ha
  · calc
      _ ≤ ∑ _j ∈ B, (1 : ℕ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
      _ = _ := by simp
  · omega

theorem rightWeights_le_card {h J : ℕ} (o : Occurrences h J) (P d : ℤ)
    (C : Finset γ) (c : γ → ℤ) (S : Finset (Coord J (512*h))) :
    rightWeights o P d C c S ≤ C.card := by
  unfold rightWeights
  split_ifs with ha
  · calc
      _ ≤ ∑ _j ∈ C, (1 : ℕ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
      _ = _ := by simp
  · omega

theorem leftSource_abs_le {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ)
    (q : GlobalOutput h J) (S : Finset (Fin (J*(512*h)))) : |leftSource P B b q S| ≤ B.card := by
  unfold leftSource SubsetTransport.reindex
  rw [Int.abs_natCast]
  exact_mod_cast leftWeights_le_card (outputOccurrences q) P B b _

theorem rightSource_abs_le {h J : ℕ} (P d : ℤ) (C : Finset γ) (c : γ → ℤ)
    (q : GlobalOutput h J) (S : Finset (Fin (J*(512*h)))) : |rightSource P d C c q S| ≤ C.card := by
  unfold rightSource SubsetTransport.reindex
  rw [Int.abs_natCast]
  exact_mod_cast rightWeights_le_card (outputOccurrences q) P d C c _









theorem queryValue_eq_transformPrefixValue {h J k : ℕ} (P d : ℤ)
    (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ) (q : GlobalOutput h J)
    (u : Fin J → Finset (Fin (512*h))) (hk : k ≤ J) :
    queryValue P d B C b c q k u =
      transformPrefixValue P d B C b c q (prefixIndices J k) u := by
  unfold queryValue SubsetStages.stageValue
  rw [← index_suffixDomain hk]
  exact SubsetTransport.mobius_partial_product_map (coordEquiv J (512*h)) _ _ _ _ _ _











end Histograms

end ThreeSum.BlockIndexedQuery

end

section


/-!
# Signed leaf weights and the explicit part of sparse queries

The alternating sign is separated from the query cardinality, allowing
the same leaf weights to be used in stored boxes and direct leaf reads.
-/

namespace ThreeSum.SignedLeaf

open Finset ThreeSum.SubsetAddress
open scoped BigOperators











theorem abs_value_le {W cut B C : ℕ} (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (preL preR S : Finset (Fin W))
    (hstage : stage ≤ W) (hL : (preL ∪ S).card ≤ cut) (hR : (preR ∪ S).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ C) :
    |value f g stage preL preR S| ≤ (((2^stage*B)*(2^stage*C) : ℕ) : ℤ) := by
  rw [value,abs_mul,abs_neg_one_pow,one_mul,abs_mul]
  have h₁ := SubsetStages.stageValue_abs_le f hf stage hstage (preL ∪ S) hL
  have h₂ := SubsetStages.stageValue_abs_le g hg stage hstage (preR ∪ S) hR
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
    Subset.mobius
      (fun S => SubsetStages.stageValue f stage (preL ∪ S)*
        SubsetStages.stageValue g stage (preR ∪ S)) Q =
      (-1 : ℤ)^Q.card * ∑ S ∈ Q.powerset, value f g stage preL preR S := by
  rw [Subset.mobius,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [neg_one_pow_sub (Finset.card_le_card (Finset.mem_powerset.mp hS)),value]
  ring



















































end ThreeSum.SignedLeaf

end

section


/-!
# The actual sparse-query machine returns the original raw prefix mass

All coordinate transport, prefix sizes, source bounds, and cutoff facts
are discharged for the concrete block histograms. The remaining storage
premises are precisely the arrays produced by source and box preprocessing.
-/

namespace ThreeSum.LightBlockQuery

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts

variable {lim : Limits} {P : Program}









section OriginalIndices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem queryValue_eq_prefixQuery {h J k : ℕ} (pMod shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512*h)))) (hk : k ≤ J) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % pMod + lift w.2.1*pMod + shift)-globalKey w.2.2) :
    queryValue pMod shift B C b c w.2.2 k (prefixRows (J := J) pre) =
      ((prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℕ) : ℤ) := by
  calc
    _ = transformPrefixValue pMod shift B C b c w.2.2 (prefixIndices J k) (prefixRows (J := J) pre) :=
      queryValue_eq_transformPrefixValue pMod shift B C b c w.2.2 (prefixRows (J := J) pre) hk
    _ = storedQueryValue pMod shift A B C a b c w k pre := by
      simp [storedQueryValue,hp,hkey]
    _ = _ := storedQueryValue_eq_prefixQuery pMod shift A B C a b c w pre hk















































































































end OriginalIndices

end ThreeSum.LightBlockQuery

end

section


/-! # Actual shrinking-suffix box preprocessing for an original valid block prefix -/

namespace ThreeSum.LightReportingSuffixBoxes

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds LightBlockQuery ReportingHostSuffix

variable {lim : Limits}
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]








theorem residual_le_suffix {h J k : ℕ} : residualSize h J k ≤ suffixStage J (512*h) k := by
  exact Nat.mul_le_mul_left (J-k) (by omega)






























































end ThreeSum.LightReportingSuffixBoxes

end

section


/-! # Original prefix counts fit the shrinking-suffix query word bound -/

namespace ThreeSum.ReportingHostSuffixValueBounds

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix
open scoped BigOperators

theorem abs_value_le_card {W cut stage B D : ℕ} (f g : Finset (Fin W) → ℤ)
    (preL preR Q : Finset (Fin W)) (hstage : stage ≤ W)
    (hL : (preL ∪ Q).card ≤ cut) (hR : (preR ∪ Q).card ≤ cut)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ B)
    (hg : ∀ S, S.card ≤ cut → |g S| ≤ D) :
    |ReportingHostQueryBounds.value f g stage preL preR Q| ≤
      ((2^Q.card*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) := by
  unfold ReportingHostQueryBounds.value
  rw [SignedLeaf.mobius_eq_signed_sum,abs_mul,abs_neg_one_pow,one_mul]
  calc
    _ ≤ ∑ S ∈ Q.powerset, |SignedLeaf.value f g stage preL preR S| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S ∈ Q.powerset, (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) := by
      apply Finset.sum_le_sum
      intro S hS
      have hs := Finset.mem_powerset.mp hS
      exact SignedLeaf.abs_value_le f g stage preL preR S hstage
        ((Finset.card_le_card (Finset.union_subset_union (le_refl preL) hs)).trans hL)
        ((Finset.card_le_card (Finset.union_subset_union (le_refl preR) hs)).trans hR) hf hg
    _ = _ := by simp [Nat.cast_mul]

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem prefix_count_le_word_sourceProof {h J k t : ℕ}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512*h)))) (hk : k ≤ J) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hvalueWord : (LightSparseQuery.magnitudeBound (suffixStage J (512*h) k) (suffixStage J (512*h) k)
      (residualSize h J k) t B.card C.card : ℤ) ≤ lim.word) :
    (prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℤ) ≤ lim.word := by
  have hQ : ∀ i, (outputRows w.2.2 i).card = 2*h :=
    fun i => LayerCounts.mem_vertices.mp (w.2.2 i).2.property
  have hprefix : ∀ j ∈ prefixIndices J k,
      prefixRows (J := J) pre j ⊆ outputRows w.2.2 j ∧ (prefixRows (J := J) pre j).card = h := by
    intro j hj
    exact hp.2 j (mem_prefixIndices.mp hj)
  have hQc : (querySet k (outputRows w.2.2)).card = residualSize h J k := querySet_card hk _ hQ
  have hv := abs_value_le_card
    (leftSource pMod B b w.2.2) (rightSource pMod shift C c w.2.2)
    (leftPrefix k (prefixRows (J := J) pre))
    (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre))
    (querySet k (outputRows w.2.2)) (suffixStage_le J (512*h) k)
    (left_union_card_le hk _ _ hQ (fun j hj => (hprefix j hj).2))
    (right_union_card_le hk _ _ hQ hprefix)
    (fun S _ => leftSource_abs_le pMod B b w.2.2 S)
    (fun S _ => rightSource_abs_le pMod shift C c w.2.2 S)
  change |queryValue pMod shift B C b c w.2.2 k (prefixRows (J := J) pre)| ≤ _ at hv
  rw [queryValue_eq_prefixQuery pMod shift A B C a b c w pre hk hp hkey,Int.abs_natCast,hQc] at hv
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ))
    (LightReportingSuffixBoxes.residual_le_suffix (h := h) (J := J) (k := k))
  have hmul := Nat.mul_le_mul_right
    ((2^(suffixStage J (512*h) k)*B.card)*(2^(suffixStage J (512*h) k)*C.card)) hpow
  have hm : 2^(suffixStage J (512*h) k)*
      ((2^(suffixStage J (512*h) k)*B.card)*(2^(suffixStage J (512*h) k)*C.card)) ≤
      LightSparseQuery.magnitudeBound (suffixStage J (512*h) k) (suffixStage J (512*h) k)
        (residualSize h J k) t B.card C.card := Nat.le_mul_of_pos_left _ (by omega)
  exact hv.trans ((Int.ofNat_le.mpr (hmul.trans hm)).trans hvalueWord)

end ThreeSum.ReportingHostSuffixValueBounds

end

universe u_1 u_2 u_3

theorem solution : ∀ {lim : Light.Limits} {α : Type u_1} {β : Type u_2} {γ : Type u_3} [Fintype.{u_1} α] [Fintype.{u_2} β]
  [Fintype.{u_3} γ] [inst : DecidableEq.{u_1 + 1} α] [DecidableEq.{u_2 + 1} β] [DecidableEq.{u_3 + 1} γ] {h J k t : Nat}
  (pMod shift : Int) (A : Finset.{u_1} α) (B : Finset.{u_2} β) (C : Finset.{u_3} γ) (a : α → Int) (b : β → Int)
  (c : γ → Int) (w : ThreeSum.RawReporting.Wanted.{u_1} h J α)
  (pre :
    List.{0}
      (Finset.{0}
        (Fin
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))),
  @LE.le.{0} Nat instLENat k J →
    @ThreeSum.StoredReporting.ValidPrefix h J
        (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (ThreeSum.GlobalEncoding.GlobalOutput h J)
          (@Prod.snd.{u_1, 0} α
            (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (ThreeSum.GlobalEncoding.GlobalOutput h J))
            w))
        k pre →
      And
          (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
            (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) A
            (@Prod.fst.{u_1, 0} α
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput h J))
              w))
          (@Dvd.dvd.{0} Int Int.instDvd (ThreeSum.GlobalEncoding.globalModulus h J)
            (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
              (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                  (@HMod.hMod.{0, 0, 0} Int Int Int (@instHMod.{0} Int Int.instMod)
                    (a
                      (@Prod.fst.{u_1, 0} α
                        (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (ThreeSum.GlobalEncoding.GlobalOutput h J))
                        w))
                    pMod)
                  (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                    (ThreeSum.RawIncidences.lift
                      (@Prod.fst.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (ThreeSum.GlobalEncoding.GlobalOutput h J)
                        (@Prod.snd.{u_1, 0} α
                          (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (ThreeSum.GlobalEncoding.GlobalOutput h J))
                          w)))
                    pMod))
                shift)
              (@ThreeSum.GlobalEncoding.globalKey h J
                (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (ThreeSum.GlobalEncoding.GlobalOutput h J)
                  (@Prod.snd.{u_1, 0} α
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput h J))
                    w))))) →
        @LE.le.{0} Int Int.instLEInt
            (@Nat.cast.{0} Int instNatCastInt
              (ThreeSum.LightSparseQuery.magnitudeBound
                (ThreeSum.BlockIndexedQuery.suffixStage J
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                  k)
                (ThreeSum.BlockIndexedQuery.suffixStage J
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                  k)
                (ThreeSum.LightBlockQuery.residualSize h J k) t (@Finset.card.{u_2} β B) (@Finset.card.{u_3} γ C)))
            lim.word →
          @LE.le.{0} Int Int.instLEInt
            (@Nat.cast.{0} Int instNatCastInt
              (@ThreeSum.RawReporting.prefixQuery.{u_1, u_2, u_3} α β γ inst h J
                (@ThreeSum.RawIncidences.rawOn.{u_1, u_2, u_3} α β γ h J pMod shift
                  (@SProd.sprod.{u_1, max u_2 u_3, max (max u_1 u_2) u_3} (Finset.{u_1} α)
                    (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
                    (Finset.{max (max u_2 u_3) u_1} (Prod.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)))
                    (@Finset.instSProd.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)) A
                    (@SProd.sprod.{u_2, u_3, max u_2 u_3} (Finset.{u_2} β) (Finset.{u_3} γ)
                      (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ)) (@Finset.instSProd.{u_2, u_3} β γ) B C))
                  a b c)
                w k pre))
            lim.word := by
  exact @ThreeSum.ReportingHostSuffixValueBounds.prefix_count_le_word_sourceProof

#print axioms solution
