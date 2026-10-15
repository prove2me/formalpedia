-- Prove2me | solution 1 for ThreeSum.ReportingHostTerminalBatch.hit_of_compatible
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:30:49.939+00:00
-- url     : https://prove2.me/submissions/0a816561-8223-49a3-adef-8cc6b132fbae

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
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
import Mathlib.Data.Finset.Range
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
import Mathlib.Data.List.ProdSigma
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
import Theorems.Thm_ThreeSum_BlockForced_forced_disjoint
import Theorems.Thm_ThreeSum_BlockForced_forced_union
import Theorems.Thm_ThreeSum_ReportingHostTerminalChoices_mem_choices


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
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockSourceBuild
end ThreeSum.LightBlockSourceBuild
namespace ThreeSum.LightReportingTerminalMasks
end ThreeSum.LightReportingTerminalMasks
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostBlockBucketTest
end ThreeSum.ReportingHostBlockBucketTest
namespace ThreeSum.ReportingHostTerminalChoices
end ThreeSum.ReportingHostTerminalChoices
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

@[simp] theorem mem_flat {J L : ℕ} {u : Fin J → Finset (Fin L)}
    {i : Fin J} {x : Fin L} : Sigma.mk i x ∈ flat u ↔ x ∈ u i := by
  simp only [flat, mem_join, Finset.mem_univ, true_and]





@[simp] theorem row_flat {J L : ℕ} (u : Fin J → Finset (Fin L)) (i : Fin J) :
    row (flat u) i = u i := by ext x; simp










theorem row_subset {J L : ℕ} {S T : Finset (Coord J L)} (h : S ⊆ T) (i : Fin J) :
    row S i ⊆ row T i := by
  intro x hx
  exact mem_row.mpr (h (mem_row.mp hx))

















theorem join_union_compl {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    join I u ∪ join Iᶜ u = flat u := by
  ext ⟨i, x⟩
  simp only [Finset.mem_union, mem_join, Finset.mem_compl, mem_flat]
  tauto













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
































section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]









































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


















































section WeightedCounts

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]









































































end WeightedCounts

end ThreeSum.BlockForced

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


/-!
# Exact stored-subset queries for the concrete reporting tree

A malformed prefix has zero mass. Every valid prefix is evaluated by the
stored suffix-zeta stages and the signed subset formula. These values are
proved to equal the natural raw-incidence fiber counts at every tree node.
-/

namespace ThreeSum.StoredReporting

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding BlockForced

private theorem ofFn_take_eq_iff {α : Type*} {J k : ℕ} (f g : Fin J → α) :
    (List.ofFn f).take k = (List.ofFn g).take k ↔ ∀ i : Fin J, i.val < k → f i = g i := by
  constructor
  · intro he i hi
    have hh := congrArg (fun xs => xs[i.val]?) he
    simpa only [List.getElem?_take_of_lt hi, List.getElem?_ofFn, dif_pos i.isLt,
      Option.some.injEq] using hh
  · intro h
    apply List.ext_getElem?
    intro i
    by_cases hi : i < k
    · rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi]
      by_cases hiJ : i < J
      · simp only [List.getElem?_ofFn, dif_pos hiJ, h ⟨i, hiJ⟩ hi]
      · simp only [List.getElem?_ofFn, dif_neg hiJ]
    · simp only [List.getElem?_take, hi, ite_false]









theorem take_prefixRows {J L k : ℕ} (pre : List (Finset (Fin L)))
    (hp : pre.length = k) (hk : k ≤ J) : (List.ofFn (prefixRows (J := J) pre)).take k = pre := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < k
  · have hiJ : i < J := hi.trans_le hk
    have hip : i < pre.length := hp ▸ hi
    simp only [List.getElem?_take_of_lt hi, List.getElem?_ofFn, dif_pos hiJ, prefixRows,
      List.getElem?_eq_getElem hip, Option.getD_some]
  · rw [List.getElem?_take_eq_none (Nat.le_of_not_lt hi),
      List.getElem?_eq_none (by omega)]

theorem completions_eq_completedTuples {h J k : ℕ} (q : GlobalOutput h J)
    (u : Fin J → Finset (Fin (512 * h))) :
    completions q k ((List.ofFn u).take k) = completedTuples q (prefixIndices J k) u := by
  ext t
  simp only [completions, completedTuples, Finset.mem_filter, Finset.mem_univ, true_and,
    partitionWord, ofFn_take_eq_iff, mem_prefixIndices]











section Indices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]



































































































































end Indices

end ThreeSum.StoredReporting

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































































theorem querySet_card {J L h k : ℕ} (hk : k ≤ J) (Q : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h) : (querySet k Q).card = (J-k)*(2*h) := by
  rw [querySet,indexSet_card,remaining,join_card_of_balance _ _ (fun i _ => hQ i),
    Finset.card_compl,Fintype.card_fin,prefixIndices_card hk]
























section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]






































































end Histograms

end ThreeSum.BlockIndexedQuery

end

section


/-!
# Costed signed residue conversion

This loop uses the benchmark's proved division-free remainder procedure.
Its sign argument supports either an ordinary histogram or a histogram of
the negated original integers. All source multiplicities are retained.
The logarithmic scratch region is reused for each input element.
-/

namespace ThreeSum.LightResidues

open Light

variable {lim : Limits} {P : Program} {d : ℕ}



theorem residue_cast {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (residue p c x : ℤ) = (c * x) % (p : ℤ) := by
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by exact_mod_cast hp.ne')












































































































end ThreeSum.LightResidues

end

section


/-!
# Original-input residue keys with a carry offset

The source histogram uses `(x % p + shift) % m`, with two independently
chosen moduli. This procedure computes both remainders from each original
signed input and retains every incidence, including duplicate values.
-/

namespace ThreeSum.LightSourceResidues

open Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000



theorem key_cast {p m : ℕ} (hm : 0 < m) (shift x : ℤ) :
    (key p m shift x : ℤ) = (x % (p : ℤ) + shift) % (m : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne'))






























variable {lim : Limits} {P : Program} {d : ℕ}

















































































































end ThreeSum.LightSourceResidues

end

section


/-!
# Original-input histograms give the exact independently trimmed sources

The histogram keys retain the first modular reduction and the signed carry
offset. Looking up the endpoint's final residue therefore counts precisely
the original divisibility condition in `BlockEncoding`. An explicit finite
enumeration accounts for every original input incidence once.
-/

namespace ThreeSum.BlockSourceEncoding

open Finset BlockEncoding GlobalEncoding LocalCoverBounds LightSourceResidues
open scoped BigOperators

set_option maxHeartbeats 1000000

theorem key_eq_iff {p m : ℕ} (hm : 0 < m) (shift x endpoint : ℤ) :
    key p m shift x = LightResidues.residue m 1 endpoint ↔
      (m : ℤ) ∣ x % (p : ℤ) + shift - endpoint := by
  rw [← Int.natCast_inj, key_cast hm, LightResidues.residue_cast hm, one_mul,
    Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]





























theorem modulus_pos (h J : ℕ) : 0 < modulus h J := pow_pos (localPrime_pos h) J

@[simp] theorem modulus_cast (h J : ℕ) : (modulus h J : ℤ) = globalModulus h J := by
  simp only [modulus,globalModulus,Nat.cast_pow]

section OriginalSources

variable {β : Type*} [DecidableEq β]



























end OriginalSources

end ThreeSum.BlockSourceEncoding

end

section


/-!
# Query-coordinate lists and weighted subset semantics

The coordinate list has one entry per set bit of the query. Its powers
form a compact weight table for the output-sensitive enumeration routine.
-/

namespace ThreeSum.QueryCoordinates

open Finset ThreeSum.SubsetAddress
open scoped BigOperators





























@[simp] theorem positions_length {W : ℕ} (Q : Finset (Fin W)) :
    (positions Q W).length = Q.card := by
  rw [← List.toFinset_card_of_nodup (positions_nodup Q W),positions_toFinset,natPositions_card]







































@[simp] theorem setLayer_length (xs : List ℕ) (k : ℕ) :
    (setLayer xs k).length = xs.length.choose k := by
  simp [setLayer,List.length_sublistsLen]











































































































































@[simp] theorem missingSets_length {W : ℕ} (Q : Finset (Fin W)) (k : ℕ) :
    (missingSets Q k).length = Q.card.choose k := by
  simp [missingSets]
























end ThreeSum.QueryCoordinates

end

section


/-!
# Finite terminal completions in the actual mask enumerator's order

At any valid reporting prefix, a full balanced endpoint needs exactly
`(J-k)*h` of the remaining query coordinates. Enumerating that one layer
contains every retained completion and costs no more than the terminal
Boolean-cube allowance. The selected bucket pair masses sum to at most the
unchanged original raw prefix count.
-/

namespace ThreeSum.ReportingHostTerminalChoices

open Finset BlockRows BlockIndex BlockEncoding BlockForced BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open QueryCoordinates
open scoped BigOperators

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000




theorem choices_length {h J k : ℕ} (q : GlobalOutput h J) (hk : k≤J) :
    (choices q k).length = ((J-k)*(2*h)).choose ((J-k)*h) := by
  simp only [choices,List.length_map,missingSets_length]
  rw [querySet_card hk (outputRows q) (fun i => LayerCounts.mem_vertices.mp (q i).2.property)]




























theorem residual_card {h J k : ℕ} (t : ChoiceTuple h J) (hk : k≤J) :
    (residual (prefixIndices J k) t).card=(J-k)*h := by
  rw [BlockForced.residual,join_card_of_balance _ _ (fun i _ => (LocalGraph.edge_data (edge (t i))).1),
    Finset.card_compl,Fintype.card_fin,prefixIndices_card hk]

theorem completion_as_completed {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hk : k≤J) (hp : ValidPrefix q k pre) :
    completions q k pre=completedTuples q (prefixIndices J k) (prefixRows pre) := by
  rw [← completions_eq_completedTuples,take_prefixRows pre hp.1 hk]

theorem completion_residual_mem {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hk : k≤J)
    (t : ChoiceTuple h J) (ht : t∈completions q k pre) :
    residual (prefixIndices J k) t ∈ choices q k := by
  apply (mem_choices q k _).mpr
  exact ⟨residual_subset q _ t (Finset.mem_filter.mp ht).2.1,residual_card t hk⟩

theorem completion_endpoints {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hk : k≤J) (hp : ValidPrefix q k pre)
    (t : ChoiceTuple h J) (ht : t∈completions q k pre) :
    prefixLeft (prefixIndices J k) (prefixRows pre) ∪ residual (prefixIndices J k) t=leftSubset t ∧
      prefixRight (prefixIndices J k) (outputRows q) (prefixRows pre) ∪
        (remaining (prefixIndices J k) (outputRows q) \ residual (prefixIndices J k) t)=rightSubset t := by
  rw [completion_as_completed q pre hk hp] at ht
  exact ⟨forced_left_completion q _ _ t ht,
    forced_right_completion q _ _ (fun i hi => (hp.2 i (mem_prefixIndices.mp hi)).1) t ht⟩

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
























end ThreeSum.ReportingHostTerminalChoices

end

section


/-!
# Actual terminal completion mask arrays

The existing exact coordinate enumerator is applied to the entire remaining
query set. It emits both full endpoint masks, so the independent endpoint
and bucket-test constructors can consume them without constructing tuples
or invoking an oracle. Every original retained completion occurs.
-/

namespace ThreeSum.LightReportingTerminalMasks

open Light Finset BlockRows BlockIndex BlockEncoding BlockForced BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open QueryCoordinates ReportingHostTerminalChoices ThreeSum.SubsetAddress

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

















theorem choiceAt_eq_get {h J k i : ℕ} (q : GlobalOutput h J) (hi : i<(choices q k).length) :
    choiceAt q k i=(choices q k)[i] := by
  simp only [choiceAt,List.getElem?_eq_getElem hi,Option.getD_some]

theorem completion_index {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hk : k≤J) (hp : ValidPrefix q k pre)
    (t : ChoiceTuple h J) (ht : t∈completions q k pre) :
    ∃ i<count h J k, leftAt q k pre i=leftSubset t ∧ rightAt q k pre i=rightSubset t := by
  obtain ⟨i,hi,hget⟩ := List.mem_iff_getElem.mp (completion_residual_mem q pre hk t ht)
  refine ⟨i,by simpa only [choices_length q hk,count] using hi,?_⟩
  rw [leftAt,rightAt,choiceAt_eq_get q hi,hget]
  exact completion_endpoints q pre hk hp t ht


























variable {lim : Limits} {d : ℕ}















































end ThreeSum.LightReportingTerminalMasks

end

section


/-!
# Exact original-encoding semantics and cost of the executed terminal batch

This is the specialization of the actual seven-procedure batch to the full
endpoint masks emitted at a valid partial prefix. The precise ordered
candidate sum is charged to raw prefix mass plus the terminal cube term.
-/

namespace ThreeSum.ReportingHostTerminalBatch

open Finset BlockRows BlockIndex BlockEncoding BlockForced BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open ReportingHostTerminalChoices ReportingHostBlockBucketTest BlockSourceEncoding LightSourceResidues
open LightReportingTerminalMasks LightBlockSourceBuild
open scoped BigOperators

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false






























































variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]























theorem hit_of_compatible_sourceProof {h J k NL NR : ℕ} (p : ℕ) (shift av : ℤ)
    (B : Finset β) (C : Finset γ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (q : GlobalOutput h J) (pre : List (Finset (Fin (512*h)))) (hk : k≤J) (hp : ValidPrefix q k pre)
    (t : ChoiceTuple h J) (ht : t∈completions q k pre) (bc : β×γ)
    (hbc : bc∈compatiblePairs (p : ℤ) shift B C b c t) (heq : c bc.2-b bc.1-av=0) :
    Hit av p shift left right NL NR q k pre := by
  have hq := (Finset.mem_filter.mp ht).2.1
  obtain ⟨s,hs,hL,hR⟩ := completion_index q pre hk hp t ht
  obtain ⟨hmem,hdivL,hdivR⟩ := Finset.mem_filter.mp hbc
  obtain ⟨hb,hc⟩ := Finset.mem_product.mp hmem
  let i : Fin NL := eL.symm ⟨bc.1,hb⟩
  let j : Fin NR := eR.symm ⟨bc.2,hc⟩
  have hi : left i.val=b bc.1 := (hvL i).trans (by simp [i])
  have hj : right j.val=c bc.2 := (hvR j).trans (by simp [j])
  refine ⟨s,hs,?_,?_,i.val,i.isLt,j.val,j.isLt,?_,?_,?_⟩
  · change leftFlag (outputOccurrences q) (leftAt q k pre s)=1
    rw [hL]
    simp [leftFlag,leftAllowed_choice t q hq]
  · change rightFlag (outputOccurrences q) (rightAt q k pre s)=1
    rw [hR]
    simp [rightFlag,rightAllowed_choice t q hq]
  · apply (key_eq_iff (modulus_pos h J) 0 (left i.val) _).mpr
    change (modulus h J : ℤ) ∣ left i.val%(p : ℤ)+0-endpointLeft (outputOccurrences q) (leftAt q k pre s)
    simpa only [hi,hL,endpointLeft_choice t q hq,modulus_cast,add_zero] using hdivL
  · apply (key_eq_iff (modulus_pos h J) shift (right j.val) _).mpr
    change (modulus h J : ℤ) ∣ right j.val%(p : ℤ)+shift-endpointRight (outputOccurrences q) (rightAt q k pre s)
    simpa only [hj,hR,endpointRight_choice t q hq,modulus_cast] using hdivR
  · simpa only [hi,hj] using heq

end ThreeSum.ReportingHostTerminalBatch

end

universe u_2 u_3

theorem solution : ∀ {β : Type u_2} {γ : Type u_3} [Fintype.{u_2} β] [Fintype.{u_3} γ] [DecidableEq.{u_2 + 1} β] [DecidableEq.{u_3 + 1} γ]
  {h J k NL NR : Nat} (p : Nat) (shift av : Int) (B : Finset.{u_2} β) (C : Finset.{u_3} γ) (b : β → Int) (c : γ → Int)
  (left right : Nat → Int) (eL : Equiv.{1, u_2 + 1} (Fin NL) ↥B) (eR : Equiv.{1, u_3 + 1} (Fin NR) ↥C),
  (∀ (i : Fin NL),
      @Eq.{1} Int (left (@Fin.val NL i))
        (b
          (@Subtype.val.{u_2 + 1} β
            (fun (x : β) =>
              @Membership.mem.{u_2, u_2} β (Finset.{u_2} β)
                (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} β) β (@Finset.instSetLike.{u_2} β)) B x)
            (@DFunLike.coe.{u_2 + 1, 1, u_2 + 1} (Equiv.{1, u_2 + 1} (Fin NL) ↥B) (Fin NL) (fun (x : Fin NL) => ↥B)
              (@EquivLike.toFunLike.{u_2 + 1, 1, u_2 + 1} (Equiv.{1, u_2 + 1} (Fin NL) ↥B) (Fin NL) (↥B)
                (@Equiv.instEquivLike.{1, u_2 + 1} (Fin NL) ↥B))
              eL i)))) →
    (∀ (j : Fin NR),
        @Eq.{1} Int (right (@Fin.val NR j))
          (c
            (@Subtype.val.{u_3 + 1} γ
              (fun (x : γ) =>
                @Membership.mem.{u_3, u_3} γ (Finset.{u_3} γ)
                  (@SetLike.instMembership.{u_3, u_3} (Finset.{u_3} γ) γ (@Finset.instSetLike.{u_3} γ)) C x)
              (@DFunLike.coe.{u_3 + 1, 1, u_3 + 1} (Equiv.{1, u_3 + 1} (Fin NR) ↥C) (Fin NR) (fun (x : Fin NR) => ↥C)
                (@EquivLike.toFunLike.{u_3 + 1, 1, u_3 + 1} (Equiv.{1, u_3 + 1} (Fin NR) ↥C) (Fin NR) (↥C)
                  (@Equiv.instEquivLike.{1, u_3 + 1} (Fin NR) ↥C))
                eR j)))) →
      ∀ (q : ThreeSum.GlobalEncoding.GlobalOutput h J)
        (pre :
          List.{0}
            (Finset.{0}
              (Fin
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))),
        @LE.le.{0} Nat instLENat k J →
          @ThreeSum.StoredReporting.ValidPrefix h J q k pre →
            ∀ (t : ThreeSum.RawIncidences.ChoiceTuple h J),
              @Membership.mem.{0, 0} (ThreeSum.RawIncidences.ChoiceTuple h J)
                  (Finset.{0} (ThreeSum.RawIncidences.ChoiceTuple h J))
                  (@SetLike.instMembership.{0, 0} (Finset.{0} (ThreeSum.RawIncidences.ChoiceTuple h J))
                    (ThreeSum.RawIncidences.ChoiceTuple h J)
                    (@Finset.instSetLike.{0} (ThreeSum.RawIncidences.ChoiceTuple h J)))
                  (@ThreeSum.RawPrefixCounts.completions h J q k pre) t →
                ∀ (bc : Prod.{u_2, u_3} β γ),
                  @Membership.mem.{max u_2 u_3, max u_3 u_2} (Prod.{u_2, u_3} β γ)
                      (Finset.{max u_2 u_3} (Prod.{u_2, u_3} β γ))
                      (@SetLike.instMembership.{max u_2 u_3, max u_2 u_3} (Finset.{max u_2 u_3} (Prod.{u_2, u_3} β γ))
                        (Prod.{u_2, u_3} β γ) (@Finset.instSetLike.{max u_2 u_3} (Prod.{u_2, u_3} β γ)))
                      (@ThreeSum.RawPrefixCounts.compatiblePairs.{u_2, u_3} β γ h J (@Nat.cast.{0} Int instNatCastInt p)
                        shift B C b c t)
                      bc →
                    @Eq.{1} Int
                        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
                          (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
                            (c (@Prod.snd.{u_2, u_3} β γ bc)) (b (@Prod.fst.{u_2, u_3} β γ bc)))
                          av)
                        (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
                      @ThreeSum.ReportingHostTerminalBatch.Hit h J av p shift left right NL NR q k pre := by
  exact @ThreeSum.ReportingHostTerminalBatch.hit_of_compatible_sourceProof

#print axioms solution
