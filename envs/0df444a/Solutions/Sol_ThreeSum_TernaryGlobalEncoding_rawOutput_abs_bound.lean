-- Prove2me | solution 1 for ThreeSum.TernaryGlobalEncoding.rawOutput_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:16:02.013426+00:00
-- url     : https://prove2.me/submissions/a687740f-f646-4b02-bdc2-3753c32d4c8a

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Theorems.Thm_ThreeSum_TernaryGlobalEncoding_rawOutput_nonnegative
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply


noncomputable section
namespace ThreeSum.TernaryGlobalEncoding
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ} [Fact p.Prime] {α π : DigitType}
variable {I Ω : Type*} [Fintype I] [Fintype Ω] [DecidableEq Ω]
variable (maps : I → Coordinate (Fin L) → ZMod p) (occ : Ω → I)
  (edge : Ω → LocalEdge L α π)
private theorem rawDot_upper (w : Coordinate (Fin L) → ZMod p) (a : TritWord L) :
    (∑ i, ((w (Sum.inl i)).val : ℤ)*(a i).val) ≤ (2*L : ℕ)*p := by
  calc
    _ ≤ ∑ _i : Fin L, (2 : ℤ)*(p : ℤ) := by
      apply sum_le_sum
      intro i _
      have hw : ((w (Sum.inl i)).val : ℤ) ≤ p := by
        have h := (w (Sum.inl i)).val_lt
        exact_mod_cast h.le
      have ha : ((a i).val : ℤ) ≤ 2 := by have h := (a i).isLt; omega
      have hw0 : (0 : ℤ) ≤ (w (Sum.inl i)).val := by positivity
      have ha0 : (0 : ℤ) ≤ (a i).val := by positivity
      nlinarith
    _ = _ := by simp; ring
end ThreeSum.TernaryGlobalEncoding
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryGlobalEncoding
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ} [Fact p.Prime] {α π : DigitType}
variable {I Ω : Type*} [Fintype I] [Fintype Ω] [DecidableEq Ω]
variable (maps : I → Coordinate (Fin L) → ZMod p) (occ : Ω → I)
  (edge : Ω → LocalEdge L α π)
namespace ThreeSum.TernaryGlobalEncoding
theorem _root_.solution (w : Coordinate (Fin L) → ZMod p) (q : TritWord L) :
    |rawOutput w q| ≤ ((2*L+2)*p : ℕ) := by
  rw [abs_of_nonneg (rawOutput_nonnegative w q)]
  have h0 : ((w (Sum.inr false)).val : ℤ) ≤ p := by
    exact_mod_cast (w (Sum.inr false)).val_lt.le
  have h1 : ((w (Sum.inr true)).val : ℤ) ≤ p := by
    exact_mod_cast (w (Sum.inr true)).val_lt.le
  have hs := rawDot_upper w q
  unfold rawOutput
  push_cast at *
  nlinarith
end ThreeSum.TernaryGlobalEncoding
