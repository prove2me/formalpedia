-- Prove2me | solution 1 for ThreeSum.BlockForced.completed_bucket_sum
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:09:54.971639+00:00
-- url     : https://prove2.me/submissions/c0092c9e-a8be-49bd-83b3-0d80d1c94dbe

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
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
import Theorems.Thm_ThreeSum_BlockForced_forced_disjoint
import Theorems.Thm_ThreeSum_BlockForced_forced_union


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting

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

@[simp] theorem mem_flat {J L : ℕ} {u : Fin J → Finset (Fin L)}
    {i : Fin J} {x : Fin L} : Sigma.mk i x ∈ flat u ↔ x ∈ u i := by
  simp only [flat, mem_join, Finset.mem_univ, true_and]





@[simp] theorem row_flat {J L : ℕ} (u : Fin J → Finset (Fin L)) (i : Fin J) :
    row (flat u) i = u i := by ext x; simp

@[simp] theorem flat_row {J L : ℕ} (S : Finset (Coord J L)) : flat (row S) = S := by
  ext ⟨i, x⟩; simp







theorem row_subset {J L : ℕ} {S T : Finset (Coord J L)} (h : S ⊆ T) (i : Fin J) :
    row S i ⊆ row T i := by
  intro x hx
  exact mem_row.mpr (h (mem_row.mp hx))








@[simp] theorem row_union {J L : ℕ} (S T : Finset (Coord J L)) (i : Fin J) :
    row (S ∪ T) i = row S i ∪ row T i := by ext x; simp







theorem join_union_compl {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    join I u ∪ join Iᶜ u = flat u := by
  ext ⟨i, x⟩
  simp only [Finset.mem_union, mem_join, Finset.mem_compl, mem_flat]
  tauto























































end ThreeSum.BlockRows

end

section


/-!
# Concrete retained choices and the global radix encoding

The local choice type retains the occurrence of a map in the deterministic
schedule.  Repeated chosen maps therefore keep their representation
multiplicity.  Canonical integer lifts of their one-hot coefficients feed
the radix recursion, whose coverage and cap are instantiated here with no
local-cover assumptions.
-/

namespace ThreeSum.GlobalEncoding

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments






































theorem retained_survives {h : ℕ} (c : RetainedChoice h) :
    Survives h (occurrence c) (edge c) := c.property




















































































































































































































































end ThreeSum.GlobalEncoding

end

section


/-!
# Independent trimmed endpoint histograms on the flattened block ground set

A histogram only inspects one endpoint and the occurrence vector. Its support
is exactly on independently retained balanced block subsets. Compatible
opposite endpoints reconstruct an actual retained choice tuple.
-/

namespace ThreeSum.BlockEncoding

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows














@[simp] theorem row_leftSubset {h J : ℕ} (t : ChoiceTuple h J) (i : Fin J) :
    row (leftSubset t) i = (edge (t i)).val.1 := row_flat _ _

@[simp] theorem row_rightSubset {h J : ℕ} (t : ChoiceTuple h J) (i : Fin J) :
    row (rightSubset t) i = (edge (t i)).val.2 := row_flat _ _

@[simp] theorem row_outputSubset {h J : ℕ} (q : GlobalOutput h J) (i : Fin J) :
    row (outputSubset q) i = (q i).2.val := row_flat _ _












theorem leftSubset_disjoint_right {h J : ℕ} (t : ChoiceTuple h J) :
    Disjoint (leftSubset t) (rightSubset t) := by
  apply Finset.disjoint_left.mpr
  intro ⟨i, x⟩ hL hR
  exact Finset.disjoint_left.mp (edge_data (edge (t i))).2.2
    (mem_flat.mp hL) (mem_flat.mp hR)

theorem leftSubset_union_right {h J : ℕ} (t : ChoiceTuple h J) :
    leftSubset t ∪ rightSubset t = outputSubset (tupleOutput t) := by
  ext ⟨i, x⟩
  simp only [Finset.mem_union, leftSubset, rightSubset, outputSubset, mem_flat,
    tupleOutput, blockOfChoice, output]

theorem rightSubset_eq_sdiff {h J : ℕ} (t : ChoiceTuple h J) :
    rightSubset t = outputSubset (tupleOutput t) \ leftSubset t := by
  rw [← leftSubset_union_right]
  have hd := Finset.disjoint_left.mp (leftSubset_disjoint_right t)
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  aesop

/-- The occurrence and union tuple together with the left subset determine
both endpoints, including all schedule multiplicity tags. -/
theorem tuple_eq_of_output_leftSubset {h J : ℕ} {s t : ChoiceTuple h J}
    (hq : tupleOutput s = tupleOutput t) (hL : leftSubset s = leftSubset t) : s = t := by
  have hR : rightSubset s = rightSubset t := by
    rw [rightSubset_eq_sdiff, rightSubset_eq_sdiff, hq, hL]
  funext i
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun q => (q i).1) hq
  · apply Subtype.ext
    exact Prod.ext (by simpa only [row_leftSubset, edge] using congrArg (fun S => row S i) hL)
      (by simpa only [row_rightSubset, edge] using congrArg (fun S => row S i) hR)

























private theorem positionalHash_map {α β : Type*} (p : ℤ) (f : α → β) (g : β → ℤ)
    (xs : List α) : Radix.positionalHash p g (xs.map f) =
      Radix.positionalHash p (fun a => g (f a)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, Radix.positionalHash, ih]

theorem leftAllowed_choice {h J : ℕ} (t : ChoiceTuple h J) (q : GlobalOutput h J)
    (hq : tupleOutput t = q) : LeftAllowed (outputOccurrences q) (leftSubset t) := by
  intro i
  have ho : occurrence (t i) = outputOccurrences q i := congrArg (fun q => (q i).1) hq
  refine ⟨by simpa only [row_leftSubset] using (edge_data (edge (t i))).1, ?_⟩
  have hs := (retained_survives (t i)).1
  simpa only [row_leftSubset, left, ho] using hs

theorem rightAllowed_choice {h J : ℕ} (t : ChoiceTuple h J) (q : GlobalOutput h J)
    (hq : tupleOutput t = q) : RightAllowed (outputOccurrences q) (rightSubset t) := by
  intro i
  have ho : occurrence (t i) = outputOccurrences q i := congrArg (fun q => (q i).1) hq
  refine ⟨by simpa only [row_rightSubset] using (edge_data (edge (t i))).2.1, ?_⟩
  have hs := (retained_survives (t i)).2
  simpa only [row_rightSubset, right, ho] using hs

theorem endpointLeft_choice {h J : ℕ} (t : ChoiceTuple h J) (q : GlobalOutput h J)
    (hq : tupleOutput t = q) : endpointLeft (outputOccurrences q) (leftSubset t) = tupleLeft t := by
  have hl : (List.ofFn fun i => rawHash (mapAt h (outputOccurrences q i))
      (leftWord (row (leftSubset t) i))) = (List.ofFn t).map rawLeft := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    have ho : occurrence (t i) = outputOccurrences q i := congrArg (fun q => (q i).1) hq
    simp only [Function.comp_apply, row_leftSubset, rawLeft, left, ho]
  rw [endpointLeft, hl, positionalHash_map]
  rfl

theorem endpointRight_choice {h J : ℕ} (t : ChoiceTuple h J) (q : GlobalOutput h J)
    (hq : tupleOutput t = q) : endpointRight (outputOccurrences q) (rightSubset t) = tupleRight t := by
  have hl : (List.ofFn fun i => rawHash (mapAt h (outputOccurrences q i))
      (rightWord (row (rightSubset t) i))) = (List.ofFn t).map rawRight := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    have ho : occurrence (t i) = outputOccurrences q i := congrArg (fun q => (q i).1) hq
    simp only [Function.comp_apply, row_rightSubset, rawRight, right, ho]
  rw [endpointRight, hl, positionalHash_map]
  rfl










@[simp] theorem leftSubset_fromSubsets {h J : ℕ} (o : Occurrences h J)
    (S V : Finset (Coord J (512 * h))) (hS : LeftAllowed o S)
    (hV : RightAllowed o V) (hd : Disjoint S V) :
    leftSubset (fromSubsets o S V hS hV hd) = S := flat_row S






theorem output_fromSubsets {h J : ℕ} (q : GlobalOutput h J)
    (S V : Finset (Coord J (512 * h))) (hS : LeftAllowed (outputOccurrences q) S)
    (hV : RightAllowed (outputOccurrences q) V) (hd : Disjoint S V)
    (hu : S ∪ V = outputSubset q) :
    tupleOutput (fromSubsets (outputOccurrences q) S V hS hV hd) = q := by
  funext i
  dsimp only [tupleOutput, blockOfChoice, fromSubsets, occurrence, edge]
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simpa only [row_union, row_outputSubset, output] using congrArg (fun S => row S i) hu

section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]





























theorem leftWeights_choice {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ)
    (t : ChoiceTuple h J) (q : GlobalOutput h J) (hq : tupleOutput t = q) :
    leftWeights (outputOccurrences q) P B b (leftSubset t) = leftBucket P B b t := by
  simp only [leftWeights, leftAllowed_choice t q hq, ite_true, endpointLeft_choice t q hq,
    leftBucket]

theorem rightWeights_choice {h J : ℕ} (P d : ℤ) (C : Finset γ) (c : γ → ℤ)
    (t : ChoiceTuple h J) (q : GlobalOutput h J) (hq : tupleOutput t = q) :
    rightWeights (outputOccurrences q) P d C c (rightSubset t) = rightBucket P d C c t := by
  simp only [rightWeights, rightAllowed_choice t q hq, ite_true, endpointRight_choice t q hq,
    rightBucket]

end Histograms

end ThreeSum.BlockEncoding

end

section


/-!
# Actual forced-prefix endpoint decompositions

Fixing completed blocks partitions each full retained tuple into its fixed
left/right subsets and its remaining left subset. The reconstruction is a
bijection, which identifies every prefix bucket sum with the subset formula.
-/

namespace ThreeSum.BlockForced

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding

section FiniteRows

variable {J L : ℕ}










private theorem suffix_not_prefix {I : Finset (Fin J)} {Q : Fin J → Finset (Fin L)}
    {x : Finset (Coord J L)} (hx : x ⊆ remaining I Q) {i : Fin J} (hi : i ∈ I)
    (a : Fin L) : Sigma.mk i a ∉ x := by
  intro ha
  exact (Finset.mem_compl.mp (mem_join.mp (hx ha)).1) hi
















































theorem row_forced_prefix (I : Finset (Fin J)) (Q u : Fin J → Finset (Fin L))
    (x : Finset (Coord J L)) (hx : x ⊆ remaining I Q) {i : Fin J} (hi : i ∈ I) :
    row (prefixLeft I u ∪ x) i = u i := by
  ext a
  simp only [mem_row, Finset.mem_union, prefixLeft, mem_join, hi, true_and,
    suffix_not_prefix hx hi a, or_false]

theorem suffix_forced_prefix (I : Finset (Fin J)) (Q u : Fin J → Finset (Fin L))
    (x : Finset (Coord J L)) (hx : x ⊆ remaining I Q) :
    join Iᶜ (row (prefixLeft I u ∪ x)) = x := by
  ext ⟨i, a⟩
  by_cases hi : i ∈ I
  · simp only [mem_join, Finset.mem_compl, hi, not_true_eq_false, false_and,
      suffix_not_prefix hx hi a]
  · simp only [mem_join, Finset.mem_compl, hi, not_false_eq_true, true_and,
      mem_row, Finset.mem_union, prefixLeft, mem_join, false_and, false_or]

theorem forced_left_of_agreement (I : Finset (Fin J)) (u v : Fin J → Finset (Fin L))
    (hv : ∀ i ∈ I, v i = u i) :
    prefixLeft I u ∪ join Iᶜ v = flat v := by
  have he : join I u = join I v := by
    ext ⟨i, a⟩
    by_cases hi : i ∈ I
    · simp only [mem_join, hi, true_and, hv i hi]
    · simp only [mem_join, hi, false_and]
  rw [prefixLeft, he]
  exact join_union_compl I v

private theorem sdiff_of_disjoint_union {S V Q : Finset (Coord J L)}
    (hd : Disjoint S V) (hu : S ∪ V = Q) : V = Q \ S := by
  rw [← hu]
  have hd' := Finset.disjoint_left.mp hd
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  aesop

end FiniteRows











theorem residual_subset {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (t : ChoiceTuple h J) (hq : tupleOutput t = q) : residual I t ⊆ remaining I (outputRows q) := by
  have hL : leftSubset t ⊆ outputSubset q := by
    rw [← hq, ← leftSubset_union_right]
    exact Finset.subset_union_left
  intro ⟨i, a⟩ hx
  obtain ⟨hi, ha⟩ := mem_join.mp hx
  apply mem_join.mpr
  refine ⟨hi, ?_⟩
  have hh := row_subset hL i
  simp only [row_leftSubset, row_outputSubset] at hh
  exact hh ha

theorem forced_left_completion {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h))) (t : ChoiceTuple h J)
    (ht : t ∈ completedTuples q I u) : prefixLeft I u ∪ residual I t = leftSubset t :=
  forced_left_of_agreement I u _ (Finset.mem_filter.mp ht).2.2

theorem forced_right_completion {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h)))
    (hu : ∀ i ∈ I, u i ⊆ outputRows q i) (t : ChoiceTuple h J)
    (ht : t ∈ completedTuples q I u) :
    prefixRight I (outputRows q) u ∪ (remaining I (outputRows q) \ residual I t) =
      rightSubset t := by
  have hq := (Finset.mem_filter.mp ht).2.1
  have hx := residual_subset q I t hq
  have he := sdiff_of_disjoint_union (forced_disjoint I (outputRows q) u (residual I t) hx)
    (forced_union I (outputRows q) u hu (residual I t) hx)
  rw [he, forced_left_completion q I u t ht, rightSubset_eq_sdiff, hq]
  rfl








theorem residual_mem {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h)))
    (hu : ∀ i ∈ I, u i ⊆ outputRows q i) (t : ChoiceTuple h J)
    (ht : t ∈ completedTuples q I u) : residual I t ∈ admissibleResiduals q I u := by
  have hq := (Finset.mem_filter.mp ht).2.1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr (residual_subset q I t hq), ?_⟩
  rw [forced_left_completion q I u t ht, forced_right_completion q I u hu t ht]
  exact ⟨leftAllowed_choice t q hq, rightAllowed_choice t q hq⟩

theorem residual_injective {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h))) :
    Set.InjOn (residual (h := h) I) (↑(completedTuples q I u) : Set (ChoiceTuple h J)) := by
  intro s hs t ht he
  apply tuple_eq_of_output_leftSubset
  · exact (Finset.mem_filter.mp hs).2.1.trans (Finset.mem_filter.mp ht).2.1.symm
  · rw [← forced_left_completion q I u s hs, ← forced_left_completion q I u t ht, he]

theorem residual_surjective {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h))) (hu : ∀ i ∈ I, u i ⊆ outputRows q i)
    (x : Finset (Coord J (512 * h))) (hx : x ∈ admissibleResiduals q I u) :
    ∃ t ∈ completedTuples q I u, residual I t = x := by
  obtain ⟨hx, hL, hR⟩ := Finset.mem_filter.mp hx
  have hxs := Finset.mem_powerset.mp hx
  let S := prefixLeft I u ∪ x
  let V := prefixRight I (outputRows q) u ∪ (remaining I (outputRows q) \ x)
  have hd : Disjoint S V := forced_disjoint I (outputRows q) u x hxs
  let t := fromSubsets (outputOccurrences q) S V hL hR hd
  have hq : tupleOutput t = q := output_fromSubsets q S V hL hR hd
    (forced_union I (outputRows q) u hu x hxs)
  have hleft : leftSubset t = S := leftSubset_fromSubsets _ _ _ _ _ _
  refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq, ?_⟩, ?_⟩
  · intro i hi
    have he := congrArg (fun S => row S i) hleft
    simpa only [row_leftSubset, S, row_forced_prefix I (outputRows q) u x hxs hi] using he
  · change join Iᶜ (fun i => (edge (t i)).val.1) = x
    have he : (fun i => (edge (t i)).val.1) = row S := by
      funext i
      simpa only [row_leftSubset] using congrArg (fun S => row S i) hleft
    rw [he]
    exact suffix_forced_prefix I (outputRows q) u x hxs

section WeightedCounts

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

theorem completed_bucket_sum_sourceProof {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h))) (hu : ∀ i ∈ I, u i ⊆ outputRows q i) :
    (∑ t ∈ completedTuples q I u, leftBucket P B b t * rightBucket P d C c t) =
      ∑ x ∈ (remaining I (outputRows q)).powerset,
        leftWeights (outputOccurrences q) P B b (prefixLeft I u ∪ x) *
        rightWeights (outputOccurrences q) P d C c
          (prefixRight I (outputRows q) u ∪ (remaining I (outputRows q) \ x)) := by
  calc
    _ = ∑ x ∈ admissibleResiduals q I u,
        leftWeights (outputOccurrences q) P B b (prefixLeft I u ∪ x) *
        rightWeights (outputOccurrences q) P d C c
          (prefixRight I (outputRows q) u ∪ (remaining I (outputRows q) \ x)) := by
      apply Finset.sum_bij (fun t _ => residual I t)
      · exact residual_mem q I u hu
      · intro s hs t ht he
        exact residual_injective q I u hs ht he
      · intro x hx
        obtain ⟨t, ht, he⟩ := residual_surjective q I u hu x hx
        exact ⟨t, ht, he⟩
      · intro t ht
        have hq := (Finset.mem_filter.mp ht).2.1
        rw [forced_left_completion q I u t ht, forced_right_completion q I u hu t ht,
          leftWeights_choice P B b t q hq, rightWeights_choice P d C c t q hq]
    _ = _ := by
      rw [admissibleResiduals, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hL : LeftAllowed (outputOccurrences q) (prefixLeft I u ∪ x)
      · by_cases hR : RightAllowed (outputOccurrences q)
            (prefixRight I (outputRows q) u ∪ (remaining I (outputRows q) \ x))
        · simp only [hL, hR, and_self, ite_true]
        · simp only [hL, hR, and_false, ite_false, rightWeights, mul_zero]
      · simp only [hL, false_and, ite_false, leftWeights, zero_mul]






































end WeightedCounts

end ThreeSum.BlockForced

end

universe u_1 u_2

theorem solution : ∀ {β : Type u_1} {γ : Type u_2} [Fintype.{u_1} β] [Fintype.{u_2} γ] [DecidableEq.{u_1 + 1} β] [DecidableEq.{u_2 + 1} γ]
  {h J : Nat} (P d : Int) (B : Finset.{u_1} β) (C : Finset.{u_2} γ) (b : β → Int) (c : γ → Int)
  (q : ThreeSum.GlobalEncoding.GlobalOutput h J) (I : Finset.{0} (Fin J))
  (u :
    Fin J →
      Finset.{0}
        (Fin
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))),
  (∀ (i : Fin J),
      @Membership.mem.{0, 0} (Fin J) (Finset.{0} (Fin J))
          (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin J)) (Fin J) (@Finset.instSetLike.{0} (Fin J))) I i →
        @LE.le.{0}
          (Finset.{0}
            (Fin
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
          (@Preorder.toLE.{0}
            (Finset.{0}
              (Fin
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
            (@PartialOrder.toPreorder.{0}
              (Finset.{0}
                (Fin
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
              (@Finset.instPartialOrder.{0}
                (Fin
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))))
          (u i) (@ThreeSum.BlockForced.outputRows h J q i)) →
    @Eq.{1} Nat
      (∑ t ∈ @ThreeSum.BlockForced.completedTuples h J q I u,
        @HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@ThreeSum.RawIncidences.leftBucket.{u_1} β h J P B b t)
          (@ThreeSum.RawIncidences.rightBucket.{u_2} γ h J P d C c t))
      (∑
        x ∈
          @Finset.powerset.{0}
            (ThreeSum.BlockRows.Coord J
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
            (@ThreeSum.BlockForced.remaining J
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
              I (@ThreeSum.BlockForced.outputRows h J q)),
        @HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@ThreeSum.BlockEncoding.leftWeights.{u_1} β h J (@ThreeSum.BlockEncoding.outputOccurrences h J q) P B b
            (@Union.union.{0}
              (Finset.{0}
                (ThreeSum.BlockRows.Coord J
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
              (@Finset.instUnion.{0}
                (ThreeSum.BlockRows.Coord J
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                fun
                  (a b :
                    ThreeSum.BlockRows.Coord J
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)) =>
                @Sigma.instDecidableEqSigma.{0, 0} (Fin J)
                  (fun (_i : Fin J) =>
                    Fin
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                  (instDecidableEqFin J)
                  (fun (a : Fin J) =>
                    instDecidableEqFin
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                  a b)
              (@ThreeSum.BlockForced.prefixLeft J
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                I u)
              x))
          (@ThreeSum.BlockEncoding.rightWeights.{u_2} γ h J (@ThreeSum.BlockEncoding.outputOccurrences h J q) P d C c
            (@Union.union.{0}
              (Finset.{0}
                (ThreeSum.BlockRows.Coord J
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
              (@Finset.instUnion.{0}
                (ThreeSum.BlockRows.Coord J
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                fun
                  (a b :
                    ThreeSum.BlockRows.Coord J
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)) =>
                @Sigma.instDecidableEqSigma.{0, 0} (Fin J)
                  (fun (_i : Fin J) =>
                    Fin
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                  (instDecidableEqFin J)
                  (fun (a : Fin J) =>
                    instDecidableEqFin
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                  a b)
              (@ThreeSum.BlockForced.prefixRight J
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                I (@ThreeSum.BlockForced.outputRows h J q) u)
              (@SDiff.sdiff.{0}
                (Finset.{0}
                  (ThreeSum.BlockRows.Coord J
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
                (@Finset.instSDiff.{0}
                  (ThreeSum.BlockRows.Coord J
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                  fun
                    (a b :
                      ThreeSum.BlockRows.Coord J
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)) =>
                  @Sigma.instDecidableEqSigma.{0, 0} (Fin J)
                    (fun (_i : Fin J) =>
                      Fin
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                    (instDecidableEqFin J)
                    (fun (a : Fin J) =>
                      instDecidableEqFin
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                    a b)
                (@ThreeSum.BlockForced.remaining J
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                  I (@ThreeSum.BlockForced.outputRows h J q))
                x)))) := by
  exact @ThreeSum.BlockForced.completed_bucket_sum_sourceProof

#print axioms solution
