-- Prove2me | solution 1 for ThreeSum.SourceBuckets.position_injective
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:52:32.56844+00:00
-- url     : https://prove2.me/submissions/394c2e10-7526-475c-a3f4-aba2fd478516

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















theorem position_start (key : ℕ → ℕ) (N i : ℕ) :
    offset key N (key i) ≤ position key N i := Nat.le_add_right _ _

theorem position_end {key : ℕ → ℕ} {N i : ℕ} (hi : i < N) :
    position key N i < offset key N (key i+1) := by
  rw [offset_succ]
  exact Nat.add_lt_add_left (count_strict hi rfl) _





theorem position_lt_of_key_lt {key : ℕ → ℕ} {N i j : ℕ}
    (hi : i < N) (hij : key i < key j) : position key N i < position key N j :=
  (position_end hi).trans_le ((offset_mono key N (by omega)).trans (position_start key N j))

theorem position_injective_sourceProof {key : ℕ → ℕ} {N i j : ℕ}
    (hi : i < N) (hj : j < N) (he : position key N i = position key N j) : i = j := by
  have hk : key i = key j := by
    rcases lt_trichotomy (key i) (key j) with h | h | h
    · have hh := position_lt_of_key_lt hi h
      omega
    · exact h
    · have hh := position_lt_of_key_lt hj h
      omega
  unfold position at he
  rw [hk] at he
  have hcount : count key (key j) i = count key (key j) j := by omega
  rcases lt_trichotomy i j with h | h | h
  · have hh := count_strict h hk
    omega
  · exact h
  · have hh := count_strict (r := key j) h rfl
    omega
































































































end ThreeSum.SourceBuckets

end


theorem solution : ∀ {key : Nat → Nat} {N i j : Nat},
  @LT.lt.{0} Nat instLTNat i N →
    @LT.lt.{0} Nat instLTNat j N →
      @Eq.{1} Nat (ThreeSum.SourceBuckets.position key N i) (ThreeSum.SourceBuckets.position key N j) → @Eq.{1} Nat i j := by
  exact @ThreeSum.SourceBuckets.position_injective_sourceProof

#print axioms solution
