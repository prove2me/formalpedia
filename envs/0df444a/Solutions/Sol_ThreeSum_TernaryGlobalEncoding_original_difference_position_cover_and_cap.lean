-- Prove2me | solution 1 for ThreeSum.TernaryGlobalEncoding.original_difference_position_cover_and_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:41:53.632198+00:00
-- url     : https://prove2.me/submissions/8c8d5434-ae4d-4f14-b4cf-a6e3fafd6a73

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Theorems.Thm_ThreeSum_TernaryGlobalEncoding_original_position_cover_and_cap

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
    (aInput : A → ℤ) (bInput : B → ℤ) (cInput : C → ℤ)
    (hp : p ≠ 0) (cap : ℕ)
    (hcover : ∀ a b : ZMod p, ∃ c : Ω,
      leftHash (maps (occ c)) (edge c) = a ∧ rightHash (maps (occ c)) (edge c) = b)
    (hcap : ∀ a b : ℤ,
      (Radix.localFiber (p : ℤ) (rawLeft maps occ edge) (rawRight maps occ edge) a b).card ≤ cap)
    (J : ℕ) (i : A) (j : B) (k : C)
    (htriple : (p : ℤ)^J ∣ cInput k-bInput j-aInput i) :
    1 ≤ (wantedRepresentations maps occ edge J (-bInput j) (cInput k) (aInput i)).card ∧
    (wantedRepresentations maps occ edge J (-bInput j) (cInput k) (aInput i)).card ≤ cap^J := by
  apply original_position_cover_and_cap maps occ edge (fun j => -bInput j) cInput aInput
    hp cap hcover hcap J j k i
  convert htriple using 1 <;> ring
end ThreeSum.TernaryGlobalEncoding
