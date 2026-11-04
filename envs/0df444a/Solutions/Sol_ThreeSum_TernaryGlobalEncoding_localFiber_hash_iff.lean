-- Prove2me | solution 1 for ThreeSum.TernaryGlobalEncoding.localFiber_hash_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:16:00.836757+00:00
-- url     : https://prove2.me/submissions/2b07544a-d2e6-4be6-9bda-96c2e91d5b9e

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Theorems.Thm_ThreeSum_TernaryGlobalEncoding_rawSource_cast_left
import Theorems.Thm_ThreeSum_TernaryGlobalEncoding_rawSource_cast_right
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



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
theorem _root_.solution (a b : ℤ) (c : Ω) :
    c ∈ Radix.localFiber (p : ℤ) (rawLeft maps occ edge) (rawRight maps occ edge) a b ↔
      leftHash (maps (occ c)) (edge c) = (-a : ZMod p) ∧
      rightHash (maps (occ c)) (edge c) = (b : ZMod p) := by
  simp only [Radix.localFiber,mem_filter,mem_univ,true_and]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sub,rawLeft,rawRight,Int.cast_neg,rawSource_cast_left,rawSource_cast_right]
  constructor
  · intro h
    constructor
    · linear_combination h.1
    · linear_combination -h.2
  · intro h
    constructor
    · linear_combination h.1
    · linear_combination -h.2
end ThreeSum.TernaryGlobalEncoding
