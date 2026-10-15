-- Prove2me | solution 1 for ThreeSum.SourceBuckets.position_bucket_iff
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:52:42.088845+00:00
-- url     : https://prove2.me/submissions/ce265d92-4430-49be-ac9f-29a03fb84561

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




























theorem position_bucket_iff_sourceProof {key : ℕ → ℕ} {N i r : ℕ} (hi : i < N) :
    offset key N r ≤ position key N i ∧ position key N i < offset key N (r+1) ↔ key i = r := by
  constructor
  · rintro ⟨ha,hb⟩
    rcases lt_trichotomy (key i) r with h | h | h
    · have he := (position_end hi).trans_le (offset_mono key N (show key i+1 ≤ r by omega))
      omega
    · exact h
    · have he := (offset_mono key N (show r+1 ≤ key i by omega)).trans (position_start key N i)
      omega
  · intro he
    have ha := position_start key N i
    have hb := position_end (key := key) hi
    simpa only [he] using And.intro ha hb

















































































end ThreeSum.SourceBuckets

end


theorem solution : ∀ {key : Nat → Nat} {N i r : Nat},
  @LT.lt.{0} Nat instLTNat i N →
    Iff
      (And (@LE.le.{0} Nat instLENat (ThreeSum.SourceBuckets.offset key N r) (ThreeSum.SourceBuckets.position key N i))
        (@LT.lt.{0} Nat instLTNat (ThreeSum.SourceBuckets.position key N i)
          (ThreeSum.SourceBuckets.offset key N
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
      (@Eq.{1} Nat (key i) r) := by
  exact @ThreeSum.SourceBuckets.position_bucket_iff_sourceProof

#print axioms solution
