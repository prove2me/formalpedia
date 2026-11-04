-- Prove2me | solution 1 for ThreeSum.TernarySignedReduction.carryCatalog_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:42:42.698208+00:00
-- url     : https://prove2.me/submissions/c1b6d230-5bfe-447c-b23e-6cb627516c66

import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
import Theorems.Thm_ThreeSum_TernarySignedReduction_valid_last
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero


attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedReduction
open TernarySignedDigits Finset
namespace ThreeSum.TernarySignedReduction
theorem _root_.solution (J : ℕ) : (carryCatalog J).card ≤ 2^J := by
  let takeCarry : CarryWord J → (Fin J → Fin 2) := fun c i => c i.castSucc
  have h : (carryCatalog J).card ≤ (univ : Finset (Fin J → Fin 2)).card := by
    apply card_le_card_of_injOn takeCarry
    · intro c hc; exact mem_univ _
    · intro c hc d hd he
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [valid_last (mem_carryCatalog _ |>.mp hc),valid_last (mem_carryCatalog _ |>.mp hd)]
      · exact congrFun he j
  simpa using h
end ThreeSum.TernarySignedReduction
