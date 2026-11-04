-- Prove2me | solution 1 for ThreeSum.TernaryGlobalEncoding.wanted_eq_representations
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:24:28.777193+00:00
-- url     : https://prove2.me/submissions/03ce6b2d-e047-4038-abad-6f6334b7faea

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Theorems.Thm_ThreeSum_TernaryGlobalEncoding_positionalHash_difference
import Definitions.Def_WeightedCache3SUM_Alias_322f8176f0ec5cb8


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
theorem _root_.solution (hp : p ≠ 0) (J : ℕ) (a b c : ℤ)
    (htriple : (p : ℤ)^J ∣ a+b-c) :
    wantedRepresentations maps occ edge J a b c = representations maps occ edge J (-a) b := by
  apply filter_eq_self.mpr
  intro xs hxs
  obtain ⟨_,ha,hb⟩ := (Radix.mem_representations (p : ℤ) (by exact_mod_cast hp)
    (rawLeft maps occ edge) (rawRight maps occ edge) J (-a) b xs).mp hxs
  rw [← positionalHash_difference]
  have hc := dvd_sub (dvd_sub hb ha) htriple
  have he : (b-Radix.positionalHash (p : ℤ) (rawRight maps occ edge) xs)-
      (-a-Radix.positionalHash (p : ℤ) (rawLeft maps occ edge) xs)-(a+b-c) =
      c-(Radix.positionalHash (p : ℤ) (rawRight maps occ edge) xs-
        Radix.positionalHash (p : ℤ) (rawLeft maps occ edge) xs) := by ring
  rw [he] at hc
  exact hc
end ThreeSum.TernaryGlobalEncoding
