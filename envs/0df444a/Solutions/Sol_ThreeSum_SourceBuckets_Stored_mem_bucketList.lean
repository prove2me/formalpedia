-- Prove2me | solution 1 for ThreeSum.SourceBuckets.Stored.mem_bucketList
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:21:10.465582+00:00
-- url     : https://prove2.me/submissions/d8e947d2-59ff-43dd-a46e-ed9679344eb8

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_SourceBuckets_position_bucket_iff
import Theorems.Thm_ThreeSum_SourceBuckets_position_injective


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram

section


/-!
# A linear-time histogram procedure in the benchmark language

The input is an array of already computed residue indices in `[0,p)`.
The output is cleared and incremented once per input item. Multiplicities
are retained, including repeated equal residues.
-/

namespace ThreeSum.LightHistogram

open Light Finset

variable {lim : Limits} {P : Program} {d : ℕ}










theorem count_succ (key : ℕ → ℕ) (r i : ℕ) :
    count key r (i + 1) = count key r i + if key i = r then 1 else 0 := by
  unfold count
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases heq : key i = r
  · rw [if_pos heq, Finset.card_insert_of_notMem (by simp)]
    simp [heq]
  · simp [heq]





























































































end ThreeSum.LightHistogram

end

section


/-!
# Exact positions of original indices in retained residue buckets

Counting-sort positions preserve every input incidence. The resulting fiber
segments contain no repeated physical indices even when input values agree.
All inverse-enumeration reasoning is semantic; the actual scatter program
writes these positions using a cursor and never searches an input band.
-/

namespace ThreeSum.SourceBuckets

open Finset LightHistogram

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000






theorem offset_succ (key : ℕ → ℕ) (N r : ℕ) :
    offset key N (r+1) = offset key N r+count key r N := by
  exact Finset.sum_range_succ _ _

theorem offset_mono (key : ℕ → ℕ) (N : ℕ) : Monotone (offset key N) := by
  intro r s hrs
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hrs)

theorem count_mono (key : ℕ → ℕ) (r : ℕ) : Monotone (count key r) := by
  intro i j hij
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hij))

theorem count_strict {key : ℕ → ℕ} {r i j : ℕ} (hij : i < j) (hkey : key i = r) :
    count key r i < count key r j := by
  have he := count_succ key r i
  simp only [hkey,ite_true] at he
  have hm := count_mono key r (show i+1 ≤ j by omega)
  omega

theorem offset_total {key : ℕ → ℕ} {N M : ℕ} (hkey : ∀ i < N, key i < M) :
    offset key N M = N := by
  unfold offset count
  have he := Finset.card_eq_sum_card_fiberwise
    (f := key) (s := range N) (t := range M)
    (fun i hi => Finset.mem_range.mpr (hkey i (Finset.mem_range.mp hi)))
  simpa only [Finset.card_range] using he.symm

theorem offset_le {key : ℕ → ℕ} {N M r : ℕ} (hkey : ∀ i < N, key i < M) (hr : r ≤ M) :
    offset key N r ≤ N := by
  exact (offset_mono key N hr).trans_eq (offset_total hkey)






theorem position_end {key : ℕ → ℕ} {N i : ℕ} (hi : i < N) :
    position key N i < offset key N (key i+1) := by
  rw [offset_succ]
  exact Nat.add_lt_add_left (count_strict hi rfl) _

theorem position_lt {key : ℕ → ℕ} {N M i : ℕ} (hkey : ∀ i < N, key i < M) (hi : i < N) :
    position key N i < N :=
  (position_end hi).trans_le (offset_le hkey (by have hk := hkey i hi; omega))







































theorem exists_position {key : ℕ → ℕ} {N M : ℕ} (hkey : ∀ i < N, key i < M)
    {t : ℕ} (ht : t < N) : ∃ i < N, position key N i = t := by
  let f : Fin N → Fin N := fun i => ⟨position key N i.val,position_lt hkey i.isLt⟩
  have hf : Function.Injective f := by
    intro i j he
    exact Fin.ext (position_injective i.isLt j.isLt (congrArg Fin.val he))
  obtain ⟨i,hi⟩ := Finite.surjective_of_injective hf ⟨t,ht⟩
  exact ⟨i.val,i.isLt,congrArg Fin.val hi⟩

theorem exists_bucket_position {key : ℕ → ℕ} {N M r t : ℕ}
    (hkey : ∀ i < N, key i < M) (hr : r < M) (ht : t < count key r N) :
    ∃ i < N, key i = r ∧ position key N i = offset key N r+t := by
  have htN : offset key N r+t < N := by
    have he := offset_le hkey (show r+1 ≤ M by omega)
    rw [offset_succ] at he
    omega
  obtain ⟨i,hi,he⟩ := exists_position hkey htN
  refine ⟨i,hi,?_,he⟩
  apply (position_bucket_iff hi).mp
  rw [he,offset_succ]
  omega












theorem Stored.read_bucket {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r t : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M)
    (hr : r < M) (ht : t < count key r N) :
    ∃ i < N, key i = r ∧ position key N i = offset key N r+t ∧
      μ (flat+offset key N r+t) = (i : ℤ) := by
  obtain ⟨i,hi,hki,hpos⟩ := exists_bucket_position hkey hr ht
  refine ⟨i,hi,hki,hpos,?_⟩
  simpa only [hpos,Nat.add_assoc] using H.indices i hi

theorem Stored.mem_bucketList_sourceProof {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r i : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M) (hr : r < M) :
    i ∈ bucketList μ flat (offset key N r) (count key r N) ↔ i < N ∧ key i = r := by
  simp only [bucketList,List.mem_ofFn]
  constructor
  · rintro ⟨t,he⟩
    obtain ⟨j,hj,hkj,_,hread⟩ := H.read_bucket hkey hr t.isLt
    rw [hread,Int.toNat_natCast] at he
    subst i
    exact ⟨hj,hkj⟩
  · rintro ⟨hi,hki⟩
    have ht : count key r i < count key r N := count_strict hi hki
    refine ⟨⟨count key r i,ht⟩,?_⟩
    have he := H.indices i hi
    unfold position at he
    rw [hki] at he
    simpa only [Nat.add_assoc,Int.toNat_natCast] using congrArg Int.toNat he





















end ThreeSum.SourceBuckets

end


theorem solution : ∀ {μ : Nat → Int} {key : Nat → Nat} {N M offsets flat r i : Nat},
  ThreeSum.SourceBuckets.Stored μ key N M offsets flat →
    (∀ (i : Nat), @LT.lt.{0} Nat instLTNat i N → @LT.lt.{0} Nat instLTNat (key i) M) →
      @LT.lt.{0} Nat instLTNat r M →
        Iff
          (@Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
            (ThreeSum.SourceBuckets.bucketList μ flat (ThreeSum.SourceBuckets.offset key N r)
              (ThreeSum.LightHistogram.count key r N))
            i)
          (And (@LT.lt.{0} Nat instLTNat i N) (@Eq.{1} Nat (key i) r)) := by
  exact @ThreeSum.SourceBuckets.Stored.mem_bucketList_sourceProof

#print axioms solution
