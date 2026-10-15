-- Prove2me | solution 1 for ThreeSum.QueryCoordinates.output_missingSets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:52:16.681135+00:00
-- url     : https://prove2.me/submissions/b7b5b7e3-c657-46f0-98a7-06f0be59d651

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
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
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightSubsetEnumeration
end ThreeSum.LightSubsetEnumeration
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Output-sensitive enumeration with arbitrary nonnegative coordinate weights

The existing recursive machine body is checked under a second contract.
Each output is the sum of the selected coordinate weights and the initial
prefix. The time and number of outputs remain binomial in the number of
available coordinates, independent of the size of the ambient mask.
-/

namespace ThreeSum.LightWeightedEnumeration

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress

open scoped BigOperators

variable {lim : Limits} {P : Program}


















@[simp] theorem output_length (weights : ℕ → ℕ) (L k pref : ℕ) :
    (output weights L k pref).length = L.choose k := by
  induction L generalizing k pref with
  | zero => cases k <;> simp [output]
  | succ L ih =>
    cases k with
    | zero => simp [output]
    | succ k =>
      by_cases h : k+1 ≤ L+1
      · simp [output,h,ih,Nat.choose_succ_succ,Nat.add_comm]
      · simp [output,h,Nat.choose_eq_zero_of_lt (by omega : L+1 < k+1)]





theorem output_empty {weights : ℕ → ℕ} {L k : ℕ} (hk : L < k) (pref : ℕ) :
    output weights L k pref = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [output_length,Nat.choose_eq_zero_of_lt hk]

theorem output_succ {weights : ℕ → ℕ} {L k : ℕ} (hk : k+1 ≤ L+1) (pref : ℕ) :
    output weights (L+1) (k+1) pref =
      output weights L (k+1) pref ++ output weights L k (pref+weights L) := by
  simp [output,hk]


























































































































































end ThreeSum.LightWeightedEnumeration

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








































































theorem output_eq_sublists (weight : ℕ → ℕ) (L k pref : ℕ) :
    LightWeightedEnumeration.output weight L k pref =
      (((List.range L).reverse).sublistsLen k).map
        (fun xs => ((pref+(xs.map weight).sum : ℕ) : ℤ)) := by
  induction L generalizing k pref with
  | zero => cases k <;> simp [LightWeightedEnumeration.output]
  | succ L ih =>
    cases k with
    | zero => simp [LightWeightedEnumeration.output]
    | succ k =>
      by_cases hk : k+1 ≤ L+1
      · rw [LightWeightedEnumeration.output_succ hk,ih,ih]
        simp [List.range_succ,List.reverse_append,List.sublistsLen_succ_cons,
          List.map_append,List.map_map,Function.comp_def,Nat.add_assoc]
      · rw [LightWeightedEnumeration.output_empty (by omega),List.sublistsLen_of_length_lt]
        · rfl
        · simp only [List.length_reverse,List.length_range]; omega

theorem output_congr {w v : ℕ → ℕ} {L : ℕ}
    (h : ∀ i, i < L → w i = v i) (k pref : ℕ) :
    LightWeightedEnumeration.output w L k pref =
      LightWeightedEnumeration.output v L k pref := by
  induction L generalizing k pref with
  | zero => cases k <;> rfl
  | succ L ih =>
    have hl : ∀ i, i < L → w i = v i := fun i hi => h i (by omega)
    have hh := h L (by omega)
    cases k with
    | zero => rfl
    | succ k => simp [LightWeightedEnumeration.output,ih hl,hh]

theorem sublistsLen_map (f : ℕ → ℕ) (xs : List ℕ) (k : ℕ) :
    (xs.map f).sublistsLen k = (xs.sublistsLen k).map (List.map f) := by
  induction xs generalizing k with
  | nil => cases k <;> simp
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp [List.sublistsLen_succ_cons,ih,List.map_append,List.map_map,Function.comp_def]

theorem map_range_getD (xs : List ℕ) :
    (List.range xs.length).map (fun i => xs[i]?.getD 0) = xs := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [List.getElem?_eq_getElem,hi']

theorem output_coordinates (xs : List ℕ) (k pref : ℕ) :
    LightWeightedEnumeration.output (fun i => (xs.map fun a => 2^a)[i]?.getD 0)
        xs.length k pref =
      ((xs.reverse).sublistsLen k).map
        (fun ys => ((pref+(ys.map fun a => 2^a).sum : ℕ) : ℤ)) := by
  have hw : ∀ i, i < xs.length →
      (xs.map fun a => 2^a)[i]?.getD 0 = 2^(xs[i]?.getD 0) := by
    intro i hi
    simp [List.getElem?_eq_getElem,hi]
  rw [output_congr hw,output_eq_sublists]
  have hr : xs.reverse = ((List.range xs.length).reverse).map (fun i => xs[i]?.getD 0) := by
    rw [List.map_reverse,map_range_getD]
  rw [hr,sublistsLen_map,List.map_map]
  simp only [List.map_map,Function.comp_def]



















































theorem output_missingSets_sourceProof {W : ℕ} (Q : Finset (Fin W)) (k : ℕ) :
    LightWeightedEnumeration.output (weights Q) Q.card k 0 =
      ((missingSets Q k).map subsetMask).map Nat.cast := by
  rw [← positions_length Q]
  change LightWeightedEnumeration.output
    (fun i => ((positions Q W).map fun a => 2^a)[i]?.getD 0)
    (positions Q W).length k 0 = _
  rw [output_coordinates]
  simp only [missingSets,setLayer,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro ys hy
  have hs := (List.mem_sublistsLen.mp hy).1
  have hn := (List.nodup_reverse.mpr (positions_nodup Q W)).sublist hs
  have hb : ys.toFinset ⊆ range W := by
    intro a ha
    have hm := hs.subset (List.mem_toFinset.mp ha)
    have hq : a ∈ natPositions Q := (mem_positions Q W a).mp (List.mem_reverse.mp hm) |>.2
    exact natPositions_subset Q hq
  rw [MaskDecode.subsetMask_decode (maskOf_isMask hb).1]
  simp only [Nat.zero_add]
  congr 1
  exact (List.sum_toFinset (fun a => 2^a) hn).symm

end ThreeSum.QueryCoordinates

end


theorem solution : ∀ {W : Nat} (Q : Finset.{0} (Fin W)) (k : Nat),
  @Eq.{1} (List.{0} Int)
    (ThreeSum.LightWeightedEnumeration.output (@ThreeSum.QueryCoordinates.weights W Q) (@Finset.card.{0} (Fin W) Q) k
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@List.map.{0, 0} Nat Int (@Nat.cast.{0} Int instNatCastInt)
      (@List.map.{0, 0} (Finset.{0} (Fin W)) Nat (@ThreeSum.SubsetAddress.subsetMask W)
        (@ThreeSum.QueryCoordinates.missingSets W Q k))) := by
  exact @ThreeSum.QueryCoordinates.output_missingSets_sourceProof

#print axioms solution
