-- Prove2me | solution 1 for ThreeSum.TernaryGlobalEncoding.original_position_cover_and_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:28:36.557217+00:00
-- url     : https://prove2.me/submissions/504b92cf-bb4f-4892-b465-0132b274be35

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Theorems.Thm_ThreeSum_TernaryGlobalEncoding_localFiber_hash_iff
import Theorems.Thm_ThreeSum_TernaryGlobalEncoding_wanted_eq_representations
import Definitions.Def_WeightedCache3SUM_Alias_8a1bc378764c1bfd
import Theorems.Thm_ThreeSum_Radix_representations_nonempty


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
theorem _root_.solution {A B C : Type*}
    (leftInput : A → ℤ) (rightInput : B → ℤ) (outputInput : C → ℤ)
    (hp : p ≠ 0) (cap : ℕ)
    (hcover : ∀ a b : ZMod p, ∃ c : Ω,
      leftHash (maps (occ c)) (edge c) = a ∧ rightHash (maps (occ c)) (edge c) = b)
    (hcap : ∀ a b : ℤ,
      (Radix.localFiber (p : ℤ) (rawLeft maps occ edge) (rawRight maps occ edge) a b).card ≤ cap)
    (J : ℕ) (i : A) (j : B) (k : C)
    (htriple : (p : ℤ)^J ∣ leftInput i+rightInput j-outputInput k) :
    1 ≤ (wantedRepresentations maps occ edge J (leftInput i) (rightInput j) (outputInput k)).card ∧
    (wantedRepresentations maps occ edge J (leftInput i) (rightInput j) (outputInput k)).card ≤ cap^J := by
  have hlocal (a b : ℤ) :
      (Radix.localFiber (p : ℤ) (rawLeft maps occ edge) (rawRight maps occ edge) a b).Nonempty := by
    obtain ⟨c,hc⟩ := hcover (-a : ZMod p) (b : ZMod p)
    exact ⟨c,(localFiber_hash_iff maps occ edge a b c).mpr hc⟩
  rw [wanted_eq_representations maps occ edge hp J _ _ _ htriple]
  constructor
  · exact card_pos.mpr (Radix.representations_nonempty (p : ℤ)
      (rawLeft maps occ edge) (rawRight maps occ edge) hlocal J _ _)
  · exact Radix.representations_card_le (p : ℤ) (rawLeft maps occ edge)
      (rawRight maps occ edge) cap hcap J _ _
end ThreeSum.TernaryGlobalEncoding
