-- Prove2me | solution 1 for ThreeSum.ReportingHostTerminalFrontier.frontier_time_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:10:05.39606+00:00
-- url     : https://prove2.me/submissions/4105769a-1bf1-4cc0-830b-c843884a65e2

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
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
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
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
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
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
import Mathlib.Data.Fintype.EquivFin
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
import Mathlib.Data.List.Range
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
import Mathlib.Tactic
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
import Theorems.Thm_ThreeSum_BlockForced_completed_bucket_sum
import Theorems.Thm_ThreeSum_RawPrefixCounts_prefixQuery_eq_bucketPrefixMass
import Theorems.Thm_ThreeSum_ReportingHostFrontier_mem_frontier_iff
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_localRow
import Theorems.Thm_ThreeSum_ReportingHostTerminalChoices_mem_choices
import Theorems.Thm_ThreeSum_Reporting_frontier_nodup
import Theorems.Thm_ThreeSum_StoredReporting_positivePrefix_valid


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
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockChildrenIndexed
end ThreeSum.LightBlockChildrenIndexed
namespace ThreeSum.LightBlockSourceBuild
end ThreeSum.LightBlockSourceBuild
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightReportingTerminalMasks
end ThreeSum.LightReportingTerminalMasks
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSourceBucketSelect
end ThreeSum.LightSourceBucketSelect
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
namespace ThreeSum.ReportingHostBucketTest
end ThreeSum.ReportingHostBucketTest
namespace ThreeSum.ReportingHostFrontier
end ThreeSum.ReportingHostFrontier
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostTerminalChoices
end ThreeSum.ReportingHostTerminalChoices
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
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
# Exact subset identities used by the proposed 3SUM algorithm

This module proves the algebraic identities, rather than taking the claimed
algorithm or its running time as an assumption.  `zeta` is the ordinary finite
subset sum; `mobius` is its signed inverse.  The fixed-cardinality specialization
is the identity used by the repeated histogram construction.
-/

namespace ThreeSum.Subset

open scoped BigOperators

variable {α : Type*} [DecidableEq α]































































































































































































































































/-! ## Stored partial zeta stages -/































































































































































































/-! ## Prefix reporting mass -/






/-- Refinement into all allowed next labels preserves the original weighted
mass, including multiplicity. This is a finite-sum identity, not a bound assumed
from the proposed 3SUM algorithm. -/
theorem fiberMass_conservation {β γ : Type*} [DecidableEq γ]
    (domain : Finset β) (labels : Finset γ) (label : β → γ) (weight : β → ℕ)
    (hlabels : ∀ p ∈ domain, label p ∈ labels) :
    (∑ value ∈ labels, fiberMass domain label weight value) =
      ∑ p ∈ domain, weight p := by
  exact Finset.sum_fiberwise_of_maps_to hlabels weight













































end ThreeSum.Subset

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






@[simp] theorem index_unindex {J L : ℕ} (S : Finset (Fin (J*L))) :
    indexSet (unindexSet (J := J) (L := L) S) = S := by
  ext c
  simp [unindexSet,indexSet]
























































































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

theorem count_eq_sum {p m : ℕ} (hm : 0 < m) (shift endpoint : ℤ)
    (values : ℕ → ℤ) (n : ℕ) :
    LightHistogram.count (fun i => key p m shift (values i))
      (LightResidues.residue m 1 endpoint) n =
        ∑ i ∈ range n, if (m : ℤ) ∣ values i % (p : ℤ) + shift - endpoint
          then 1 else 0 := by
  unfold LightHistogram.count
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  simp only [key_eq_iff hm]

theorem count_eq_sum_of_equiv {β : Type*} [DecidableEq β]
    {p m n : ℕ} (hm : 0 < m) (shift endpoint : ℤ)
    (B : Finset β) (b : β → ℤ) (values : ℕ → ℤ)
    (e : Fin n ≃ B) (hvalues : ∀ i : Fin n, values i.val = b (e i)) :
    LightHistogram.count (fun i => key p m shift (values i))
      (LightResidues.residue m 1 endpoint) n =
        ∑ i ∈ B, if (m : ℤ) ∣ b i % (p : ℤ) + shift - endpoint then 1 else 0 := by
  rw [count_eq_sum hm,← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ i : B, if (m : ℤ) ∣ b i % (p : ℤ) + shift - endpoint then 1 else 0 := by
      apply Fintype.sum_equiv e
      intro i
      rw [hvalues i]
    _ = _ := Finset.sum_coe_sort B
      (fun i : β => if (m : ℤ) ∣ b i % (p : ℤ) + shift - endpoint then (1 : ℕ) else 0)



theorem modulus_pos (h J : ℕ) : 0 < modulus h J := pow_pos (localPrime_pos h) J

@[simp] theorem modulus_cast (h J : ℕ) : (modulus h J : ℤ) = globalModulus h J := by
  simp only [modulus,globalModulus,Nat.cast_pow]

section OriginalSources

variable {β : Type*} [DecidableEq β]

theorem leftWeights_eq_histogram {h J n : ℕ} (o : Occurrences h J) (p : ℕ)
    (B : Finset β) (b : β → ℤ) (S : Finset (BlockRows.Coord J (512*h)))
    (values : ℕ → ℤ) (e : Fin n ≃ B)
    (hvalues : ∀ i : Fin n, values i.val = b (e i)) :
    leftWeights o (p : ℤ) B b S =
      if LeftAllowed o S then
        LightHistogram.count (fun i => key p (modulus h J) 0 (values i))
          (LightResidues.residue (modulus h J) 1 (endpointLeft o S)) n
      else 0 := by
  unfold leftWeights
  rw [count_eq_sum_of_equiv (modulus_pos h J) 0 (endpointLeft o S) B b values e hvalues]
  simp only [modulus_cast,add_zero]

theorem rightWeights_eq_histogram {h J n : ℕ} (o : Occurrences h J) (p : ℕ) (shift : ℤ)
    (C : Finset β) (c : β → ℤ) (S : Finset (BlockRows.Coord J (512*h)))
    (values : ℕ → ℤ) (e : Fin n ≃ C)
    (hvalues : ∀ i : Fin n, values i.val = c (e i)) :
    rightWeights o (p : ℤ) shift C c S =
      if RightAllowed o S then
        LightHistogram.count (fun i => key p (modulus h J) shift (values i))
          (LightResidues.residue (modulus h J) 1 (endpointRight o S)) n
      else 0 := by
  unfold rightWeights
  rw [count_eq_sum_of_equiv (modulus_pos h J) shift (endpointRight o S) C c values e hvalues]
  simp only [modulus_cast]

end OriginalSources

end ThreeSum.BlockSourceEncoding

end

section


/-!
# Actual independent bucket selection followed by original tuple testing

The host reads the two retained offset headers, applies each endpoint's
independent flag, and runs the exact original-value Cartesian scanner. Its
time is linear in the actual selected physical pair mass plus a constant.
-/

namespace ThreeSum.LightReportingBucketTest

open Light SourceBuckets LightHistogram LightSourceBucketSelect ReportingHostBucketTest

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

















variable {lim : Limits} {P : Program} {d : ℕ}













































































































theorem time_eq (keyL keyR : ℕ → ℕ) (NL NR rL rR flagL flagR : ℕ) :
    time keyL keyR NL NR rL rR flagL flagR =
      240*(countSelected keyL NL rL flagL*countSelected keyR NR rR flagR)+700 := by
  unfold time LightReportingBucketPairs.time
  ring

end ThreeSum.LightReportingBucketTest

end

section


/-!
# Actual terminal-candidate batch with a sum of physical pair charges

All endpoint and independent flag arrays are read from retained memory.
The recursion evaluates each candidate and retains a Boolean disjunction.
Its cost sums the actual leaf costs instead of multiplying a worst fiber
size by the number of candidates.
-/

namespace ThreeSum.LightReportingLeafBatch

open Light Finset SourceBuckets LightResidues
open scoped BigOperators

set_option maxHeartbeats 2600000
set_option maxRecDepth 10000

























theorem time_eq_sum (keyL keyR flagL flagR : ℕ→ℕ) (NL NR Mo U : ℕ) (xL xR : ℕ→ℤ) (n : ℕ) :
    time keyL keyR flagL flagR NL NR Mo U xL xR n=30+
      ∑ i∈range n, (LightReportingLeaf.time keyL keyR NL NR Mo (flagL i) (flagR i) U (xL i) (xR i)+300) := by
  induction n with
  | zero => simp [time]
  | succ n ih => simp only [time,Finset.sum_range_succ,ih]; omega

















variable {lim : Limits}


























































































end ThreeSum.LightReportingLeafBatch

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

theorem setLayer_nodup (xs : List ℕ) (hn : xs.Nodup) (k : ℕ) :
    (setLayer xs k).Nodup := by
  apply (List.nodup_sublistsLen k hn).map_on
  intro a ha b hb he
  have ha' := (List.mem_sublistsLen.mp ha).1
  have hb' := (List.mem_sublistsLen.mp hb).1
  apply (hn.perm_iff_eq_of_sublist ha' hb').mp
  exact List.perm_of_nodup_nodup_toFinset_eq (hn.sublist ha') (hn.sublist hb') he





















































































































theorem missingSets_nodup {W : ℕ} (Q : Finset (Fin W)) (k : ℕ) :
    (missingSets Q k).Nodup := by
  unfold missingSets
  apply (setLayer_nodup _ (List.nodup_reverse.mpr (positions_nodup Q W)) k).map_on
  intro a ha b hb he
  have has := (mem_setLayer _ (List.nodup_reverse.mpr (positions_nodup Q W)) _ _).mp ha
  have hbs := (mem_setLayer _ (List.nodup_reverse.mpr (positions_nodup Q W)) _ _).mp hb
  rw [List.toFinset_reverse,positions_toFinset] at has hbs
  have h := congrArg natPositions he
  rw [decode_maskOf (has.1.trans (natPositions_subset Q)),
      decode_maskOf (hbs.1.trans (natPositions_subset Q))] at h
  exact h

@[simp] theorem missingSets_length {W : ℕ} (Q : Finset (Fin W)) (k : ℕ) :
    (missingSets Q k).length = Q.card.choose k := by
  simp [missingSets]
























end ThreeSum.QueryCoordinates

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



























































theorem globalChildren_nodup {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (globalChildren i Q h).Nodup := QueryCoordinates.missingSets_nodup _ _



















theorem localChildren_nodup {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (localChildren i Q h).Nodup := by
  apply (globalChildren_nodup i Q h).map_on
  intro S hS T hT he
  have hs := (QueryCoordinates.missingSets_mem _ _ _).mp hS
  have ht := (QueryCoordinates.missingSets_mem _ _ _).mp hT
  rw [← blockSet_localRow i Q hs.1,← blockSet_localRow i Q ht.1,he]



























































































































































end ThreeSum.ReportingHostMasks

end

section


/-!
# Coverage and raw-mass charging in the machine's actual child order

The output-sensitive enumerator uses its recursive coordinate order. The
reporting tree is instantiated with that exact order here; its positive
frontiers retain the original incidences and their multiplicities.
-/

namespace ThreeSum.ReportingHostFrontier

open Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostMasks BlockForced
open scoped BigOperators











theorem children_nodup {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) :
    (children q k).Nodup := by
  unfold children
  split
  · exact localChildren_nodup _ _ _
  · exact List.nodup_nil









section Indices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
























omit [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ] in
theorem frontier_nodup {h J : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (k : ℕ) : (frontier I w k).Nodup :=
  Reporting.frontier_nodup _ _ (children_nodup _) _
































































end Indices

end ThreeSum.ReportingHostFrontier

end

section


/-!
# Exact next-frontier order and raw-mass charges for the actual expansion

Gathering the stably selected child positions produces exactly the recursive
reporting frontier, including its original order and retained multiplicity.
-/

namespace ThreeSum.ReportingHostPositive

open Light Finset ThreeSum.SubsetAddress
open BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open LightBlockChildrenIndexed ReportingHostFrontier
open scoped BigOperators

set_option linter.unusedSectionVars false















theorem frontier_positive {α : Type*} (children : ℕ → List α) (query : ℕ → List α → ℕ)
    {k : ℕ} {pre : List α} (hp : pre ∈ Reporting.frontier children query k) :
    0 < query k pre := by
  cases k with
  | zero =>
      simp only [Reporting.frontier] at hp
      split at hp
      · have he : pre = [] := List.mem_singleton.mp hp
        simpa only [he] using ‹0 < query 0 []›
      · cases hp
  | succ k =>
      exact of_decide_eq_true (List.mem_filter.mp hp).2

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
























theorem frontier_valid {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (hk : k ≤ J) {pre : List (Finset (Fin (512*h)))}
    (hp : pre ∈ ReportingHostFrontier.frontier I w k) : ValidPrefix w.2.2 k pre :=
  positivePrefix_valid I w pre hk (frontier_positive _ _ hp)





















end ThreeSum.ReportingHostPositive

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

theorem choices_length_le {h J k : ℕ} (q : GlobalOutput h J) (hk : k≤J) :
    (choices q k).length ≤ 2^((J-k)*(2*h)) := by
  rw [choices_length q hk]
  exact Nat.choose_le_two_pow _ _

theorem choices_nodup {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) : (choices q k).Nodup := by
  apply (missingSets_nodup _ _).map
  intro S T he
  simpa only [index_unindex] using congrArg indexSet he























theorem completion_as_completed {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hk : k≤J) (hp : ValidPrefix q k pre) :
    completions q k pre=completedTuples q (prefixIndices J k) (prefixRows pre) := by
  rw [← completions_eq_completedTuples,take_prefixRows pre hp.1 hk]


















variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]









theorem pairMass_sum_le_prefixQuery {h J k : ℕ} (P shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k≤J) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1∈A ∧ globalModulus h J ∣ (a w.1%P+lift w.2.1*P+shift)-globalKey w.2.2) :
    ((choices w.2.2 k).map (pairMass P shift B C b c w.2.2 k pre)).sum ≤
      prefixQuery (rawOn h J P shift (A ×ˢ (B ×ˢ C)) a b c) w k pre := by
  rw [← List.sum_toFinset _ (choices_nodup w.2.2 k)]
  rw [prefixQuery_eq_bucketPrefixMass,bucketPrefixMass,if_pos hkey,
    completion_as_completed w.2.2 pre hk hp,
    completed_bucket_sum P shift B C b c w.2.2 _ _
      (fun i hi => (hp.2 i (mem_prefixIndices.mp hi)).1)]
  apply Finset.sum_le_sum_of_subset
  intro S hS
  exact Finset.mem_powerset.mpr ((mem_choices w.2.2 k S).mp (List.mem_toFinset.mp hS)).1

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



































variable {lim : Limits} {d : ℕ}















































end ThreeSum.LightReportingTerminalMasks

end

section


/-!
# Original endpoint semantics and exact Cartesian-test cost

The selected physical lengths are the original independently trimmed source
weights, after transport by the original-index enumeration. Thus the actual
tuple tester's pair charge is exactly the raw leaf weight.
-/

namespace ThreeSum.ReportingHostBlockBucketTest

open Light Finset BlockRows BlockEncoding BlockSourceEncoding LightSourceResidues
open SourceBuckets LightSourceBucketSelect ReportingHostBucketTest
open GlobalEncoding RawIncidences

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000













theorem selected_left_eq_weights {β : Type*} [DecidableEq β] {h J N : ℕ}
    (o : Occurrences h J) (p : ℕ) (B : Finset β) (b : β→ℤ)
    (S : Finset (Coord J (512*h))) (v : ℕ→ℤ) (e : Fin N ≃ B)
    (hv : ∀ i : Fin N, v i.val=b (e i)) :
    countSelected (fun i => key p (modulus h J) 0 (v i)) N (leftResidue o S) (leftFlag o S)=
      leftWeights o (p : ℤ) B b S := by
  rw [leftWeights_eq_histogram o p B b S v e hv]
  unfold countSelected leftFlag leftResidue
  by_cases hs : LeftAllowed o S <;> simp [hs]

theorem selected_right_eq_weights {γ : Type*} [DecidableEq γ] {h J N : ℕ}
    (o : Occurrences h J) (p : ℕ) (shift : ℤ) (C : Finset γ) (c : γ→ℤ)
    (S : Finset (Coord J (512*h))) (v : ℕ→ℤ) (e : Fin N ≃ C)
    (hv : ∀ i : Fin N, v i.val=c (e i)) :
    countSelected (fun i => key p (modulus h J) shift (v i)) N (rightResidue o S) (rightFlag o S)=
      rightWeights o (p : ℤ) shift C c S := by
  rw [rightWeights_eq_histogram o p shift C c S v e hv]
  unfold countSelected rightFlag rightResidue
  by_cases hs : RightAllowed o S <;> simp [hs]

theorem actual_time_eq {β γ : Type*} [DecidableEq β] [DecidableEq γ] {h J NL NR : ℕ}
    (o : Occurrences h J) (p : ℕ) (shift : ℤ) (B : Finset β) (C : Finset γ)
    (b : β→ℤ) (c : γ→ℤ) (S T : Finset (Coord J (512*h))) (left right : ℕ→ℤ)
    (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j)) :
    LightReportingBucketTest.time (fun i => key p (modulus h J) 0 (left i))
      (fun j => key p (modulus h J) shift (right j)) NL NR
      (leftResidue o S) (rightResidue o T) (leftFlag o S) (rightFlag o T) =
        240*(leftWeights o (p : ℤ) B b S*rightWeights o (p : ℤ) shift C c T)+700 := by
  rw [LightReportingBucketTest.time_eq,selected_left_eq_weights o p B b S left eL hvL,
    selected_right_eq_weights o p shift C c T right eR hvR]





















end ThreeSum.ReportingHostBlockBucketTest

end

section


/-!
# Charging actual terminal scans to the original raw prefix mass

The actual independent bucket tester costs `240` per selected physical pair
plus `700` per terminal candidate. This file sums those exact verified costs
over the enumerator's unchanged order. It also proves conservation of raw
mass across the actual positive frontier at any partial depth.
-/

namespace ThreeSum.ReportingHostTerminalCosts

open Finset BlockRows BlockIndex BlockEncoding BlockForced BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open ReportingHostTerminalChoices ReportingHostBlockBucketTest BlockSourceEncoding LightSourceResidues
open scoped BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

theorem sum_linear {δ : Type*} (xs : List δ) (f : δ→ℕ) (c d : ℕ) :
    (xs.map (fun x => c*f x+d)).sum=c*(xs.map f).sum+d*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih]; ring

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]













theorem actualTestWork_eq {h J NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (B : Finset β) (C : Finset γ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (q : GlobalOutput h J) (k : ℕ) (pre : List (Finset (Fin (512*h)))) :
    actualTestWork p shift left right NL NR q k pre =
      240*((choices q k).map (pairMass (p : ℤ) shift B C b c q k pre)).sum+700*(choices q k).length := by
  unfold actualTestWork
  simp_rw [actual_time_eq (outputOccurrences q) p shift B C b c _ _ left right eL eR hvL hvR]
  exact sum_linear (choices q k) (pairMass (p : ℤ) shift B C b c q k pre) 240 700

theorem actualTestWork_le {h J k NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k≤J) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1∈A ∧ globalModulus h J ∣ (a w.1%(p : ℤ)+lift w.2.1*(p : ℤ)+shift)-globalKey w.2.2) :
    actualTestWork p shift left right NL NR w.2.2 k pre ≤
      240*prefixQuery (rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w k pre+
        700*2^((J-k)*(2*h)) := by
  rw [actualTestWork_eq p shift B C b c left right eL eR hvL hvR]
  exact Nat.add_le_add
    (Nat.mul_le_mul_left 240 (pairMass_sum_le_prefixQuery (p : ℤ) shift A B C a b c w pre hk hp hkey))
    (Nat.mul_le_mul_left 700 (choices_length_le w.2.2 hk))

theorem frontier_mass {h J k : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (hk : k≤J) :
    ((ReportingHostFrontier.frontier I w k).map (prefixQuery I w k)).sum=(domain I w).card := by
  rw [← List.sum_toFinset _ (ReportingHostFrontier.frontier_nodup I w k)]
  change (∑ pre ∈ (ReportingHostFrontier.frontier I w k).toFinset,
    Subset.fiberMass (domain I w) (fun r => (word r).take k) (fun _ => 1) pre)=(domain I w).card
  rw [Subset.fiberMass_conservation]
  · simp
  · intro r hr
    apply List.mem_toFinset.mpr
    exact (ReportingHostFrontier.mem_frontier_iff I w hk _).mpr
      ⟨r,(Finset.mem_filter.mp hr).1,(Finset.mem_filter.mp hr).2,rfl⟩








end ThreeSum.ReportingHostTerminalCosts

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























theorem sum_choiceAt {h J k : ℕ} (q : GlobalOutput h J) (hk : k≤J)
    (f : Finset (Coord J (512*h))→ℕ) :
    (∑ i∈range (count h J k), f (choiceAt q k i))=((choices q k).map f).sum := by
  rw [show count h J k=(choices q k).length by exact (choices_length q hk).symm,Finset.sum_range]
  calc
    (∑ i : Fin (choices q k).length, f (choiceAt q k i.val)) =
        ∑ i : Fin (choices q k).length, f ((choices q k)[i.val]) :=
      Finset.sum_congr rfl (fun i _ => congrArg f (choiceAt_eq_get q i.isLt))
    _ = _ := Fin.sum_univ_fun_getElem (choices q k) f

theorem time_eq {h J k : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : GlobalOutput h J) (pre : List (Finset (Fin (512*h)))) (hk : k≤J) :
    time p shift left right NL NR q k pre=
      ReportingHostTerminalCosts.actualTestWork p shift left right NL NR q k pre+
        count h J k*(2*LightResidues.residueBudget (endpointBound h J)+600)+30 := by
  unfold time
  rw [LightReportingLeafBatch.time_eq_sum]
  simp only [LightReportingLeaf.time]
  have hsum := sum_choiceAt q hk (fun S =>
    LightReportingBucketTest.time
      (fun i => key p (modulus h J) 0 (left i)) (fun i => key p (modulus h J) shift (right i)) NL NR
      (leftResidue (outputOccurrences q) (prefixLeft (prefixIndices J k) (prefixRows pre) ∪ S))
      (rightResidue (outputOccurrences q) (prefixRight (prefixIndices J k) (outputRows q) (prefixRows pre) ∪
        (remaining (prefixIndices J k) (outputRows q) \ S)))
      (leftFlag (outputOccurrences q) (prefixLeft (prefixIndices J k) (prefixRows pre) ∪ S))
      (rightFlag (outputOccurrences q) (prefixRight (prefixIndices J k) (outputRows q) (prefixRows pre) ∪
        (remaining (prefixIndices J k) (outputRows q) \ S))))
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul]
  change 30+(_+_+_+_)=_
  have hsum' : (∑ i∈range (count h J k),
      LightReportingBucketTest.time
        (fun i => key p (modulus h J) 0 (left i)) (fun i => key p (modulus h J) shift (right i)) NL NR
        (LightResidues.residue (modulus h J) 1 (endpointsLeft q k pre i))
        (LightResidues.residue (modulus h J) 1 (endpointsRight q k pre i))
        (flagsLeft q k pre i) (flagsRight q k pre i))=
      ReportingHostTerminalCosts.actualTestWork p shift left right NL NR q k pre := hsum
  rw [hsum']
  ring

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem time_le {h J k NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k≤J) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1∈A ∧ globalModulus h J ∣ (a w.1%(p : ℤ)+lift w.2.1*(p : ℤ)+shift)-globalKey w.2.2) :
    time p shift left right NL NR w.2.2 k pre ≤
      240*prefixQuery (rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w k pre+
        (2*LightResidues.residueBudget (endpointBound h J)+1300)*2^((J-k)*(2*h))+30 := by
  rw [time_eq p shift left right NL NR w.2.2 pre hk]
  have htest := ReportingHostTerminalCosts.actualTestWork_le p shift A B C a b c left right eL eR hvL hvR w pre hk hp hkey
  have hn : count h J k≤2^((J-k)*(2*h)) := Nat.choose_le_two_pow _ _
  have hmul := Nat.mul_le_mul_right (2*LightResidues.residueBudget (endpointBound h J)+600) hn
  nlinarith







































end ThreeSum.ReportingHostTerminalBatch

end

section


/-!
# Exact terminal-prefix order, summed cost, and original completeness

The prefix batch consumes the actual retained frontier order. Every local
scan keeps its own selected-pair charge; their sum is bounded by the exact
original raw mass at the partial depth.
-/

namespace ThreeSum.ReportingHostTerminalFrontier

open Finset BlockRows BlockEncoding GlobalEncoding RawIncidences RawReporting RawPrefixCounts
open StoredReporting LightBlockSourceBuild
open scoped BigOperators

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000




theorem prefixAt_eq_get {h i : ℕ} (pres : List (List (Finset (Fin (512*h))))) (hi : i<pres.length) :
    prefixAt pres i=pres[i] := by simp only [prefixAt,List.getElem?_eq_getElem hi,Option.getD_some]





































theorem time_all {h J : ℕ} (p : ℕ) (shift : ℤ) (left right : ℕ→ℤ) (NL NR : ℕ)
    (q : GlobalOutput h J) (k : ℕ) (pres : List (List (Finset (Fin (512*h))))) :
    time p shift left right NL NR q k pres pres.length=
      (pres.map (fun pre => LightReportingTerminal.time p shift left right NL NR q k pre+300)).sum+30 := by
  have hsum (n : ℕ) : time p shift left right NL NR q k pres n=
      (∑ i∈range n, (LightReportingTerminal.time p shift left right NL NR q k (prefixAt pres i)+300))+30 := by
    induction n with
    | zero => simp [time]
    | succ n ih => simp only [time,Finset.sum_range_succ,ih]; omega
  rw [hsum,Finset.sum_range]
  congr 1
  calc
    (∑ i : Fin pres.length, (LightReportingTerminal.time p shift left right NL NR q k (prefixAt pres i.val)+300)) =
        ∑ i : Fin pres.length, (LightReportingTerminal.time p shift left right NL NR q k pres[i.val]+300) :=
      Finset.sum_congr rfl (fun i _ => by rw [prefixAt_eq_get pres i.isLt])
    _ = _ := Fin.sum_univ_fun_getElem pres
      (fun pre => LightReportingTerminal.time p shift left right NL NR q k pre+300)






variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem prefix_time_le {h J k NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k≤J) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1∈A ∧ globalModulus h J ∣ (a w.1%(p : ℤ)+lift w.2.1*(p : ℤ)+shift)-globalKey w.2.2) :
    LightReportingTerminal.time p shift left right NL NR w.2.2 k pre+300 ≤
      240*prefixQuery (rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c) w k pre+charge h J k := by
  have hh := ReportingHostTerminalBatch.time_le p shift A B C a b c left right eL eR hvL hvR w pre hk hp hkey
  unfold LightReportingTerminal.time LightReportingTerminalPrepared.time charge
  omega

theorem frontier_time_le_sourceProof {h J k NL NR : ℕ} (p : ℕ) (shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (left right : ℕ→ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j))
    (w : Wanted h J α) (hk : k≤J)
    (hkey : w.1∈A ∧ globalModulus h J ∣ (a w.1%(p : ℤ)+lift w.2.1*(p : ℤ)+shift)-globalKey w.2.2) :
    let I := rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
    let pres := ReportingHostFrontier.frontier I w k
    time p shift left right NL NR w.2.2 k pres pres.length≤
      240*(domain I w).card+charge h J k*pres.length+30 := by
  dsimp only
  rw [time_all]
  let I := rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
  let pres := ReportingHostFrontier.frontier I w k
  have hsum : (pres.map (fun pre => LightReportingTerminal.time p shift left right NL NR w.2.2 k pre+300)).sum≤
      (pres.map (fun pre => 240*prefixQuery I w k pre+charge h J k)).sum := by
    apply List.sum_le_sum
    intro pre hpre
    exact prefix_time_le p shift A B C a b c left right eL eR hvL hvR w pre hk
      (ReportingHostPositive.frontier_valid I w hk hpre) hkey
  rw [ReportingHostTerminalCosts.sum_linear,ReportingHostTerminalCosts.frontier_mass I w hk] at hsum
  dsimp only [pres,I] at hsum
  omega

end ThreeSum.ReportingHostTerminalFrontier

end

universe u_1 u_2 u_3

theorem solution : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [Fintype.{u_1} α] [Fintype.{u_2} β] [Fintype.{u_3} γ]
  [inst : DecidableEq.{u_1 + 1} α] [DecidableEq.{u_2 + 1} β] [DecidableEq.{u_3 + 1} γ] {h J k NL NR : Nat} (p : Nat)
  (shift : Int) (A : Finset.{u_1} α) (B : Finset.{u_2} β) (C : Finset.{u_3} γ) (a : α → Int) (b : β → Int) (c : γ → Int)
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
      ∀ (w : ThreeSum.RawReporting.Wanted.{u_1} h J α),
        @LE.le.{0} Nat instLENat k J →
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
                        (@Nat.cast.{0} Int instNatCastInt p))
                      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                        (ThreeSum.RawIncidences.lift
                          (@Prod.fst.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (ThreeSum.GlobalEncoding.GlobalOutput h J)
                            (@Prod.snd.{u_1, 0} α
                              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                (ThreeSum.GlobalEncoding.GlobalOutput h J))
                              w)))
                        (@Nat.cast.{0} Int instNatCastInt p)))
                    shift)
                  (@ThreeSum.GlobalEncoding.globalKey h J
                    (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput h J)
                      (@Prod.snd.{u_1, 0} α
                        (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (ThreeSum.GlobalEncoding.GlobalOutput h J))
                        w))))) →
            have I :=
              @ThreeSum.RawIncidences.rawOn.{u_1, u_2, u_3} α β γ h J (@Nat.cast.{0} Int instNatCastInt p) shift
                (@SProd.sprod.{u_1, max u_2 u_3, max (max u_1 u_2) u_3} (Finset.{u_1} α)
                  (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
                  (Finset.{max (max u_2 u_3) u_1} (Prod.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)))
                  (@Finset.instSProd.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)) A
                  (@SProd.sprod.{u_2, u_3, max u_2 u_3} (Finset.{u_2} β) (Finset.{u_3} γ)
                    (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ)) (@Finset.instSProd.{u_2, u_3} β γ) B C))
                a b c;
            have pres := @ThreeSum.ReportingHostFrontier.frontier.{u_1, u_2, u_3} α β γ inst h J I w k;
            @LE.le.{0} Nat instLENat
              (@ThreeSum.ReportingHostTerminalFrontier.time h J p shift left right NL NR
                (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (ThreeSum.GlobalEncoding.GlobalOutput h J)
                  (@Prod.snd.{u_1, 0} α
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput h J))
                    w))
                k pres
                (@List.length.{0}
                  (List.{0}
                    (Finset.{0}
                      (Fin
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
                  pres))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 240) (instOfNatNat (nat_lit 240)))
                    (@Finset.card.{max (max u_1 u_2) u_3} (ThreeSum.RawIncidences.RawItem.{u_1, u_2, u_3} h J α β γ)
                      (@ThreeSum.RawReporting.domain.{u_1, u_2, u_3} α β γ inst h J I w)))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (ThreeSum.ReportingHostTerminalFrontier.charge h J k)
                    (@List.length.{0}
                      (List.{0}
                        (Finset.{0}
                          (Fin
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
                      pres)))
                (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := by
  exact @ThreeSum.ReportingHostTerminalFrontier.frontier_time_le_sourceProof

#print axioms solution
