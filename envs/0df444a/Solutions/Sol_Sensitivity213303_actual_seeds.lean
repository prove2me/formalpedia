-- Prove2me | solution 1 for Sensitivity213303.actual_seeds
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:12:38.635583+00:00
-- url     : https://prove2.me/submissions/f0c30767-15ec-4356-bf68-3b9a5f0511dd

import Definitions.Def_BS2_b3ba934b_Endpoint40Seeds
import Theorems.Thm_SensitivityPublishing213303_periodic_upper
set_option autoImplicit false

theorem solution : ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
  16^m ≤ OAI.Paper320.sensitivity f ∧
  OAI.Paper320.sensitivity f ≤ 10^69*31739938^m ∧
  (10007^4)^m ≤ OAI.Paper320.blockSensitivity f := by
  intro m
  obtain ⟨n,f,hs,hupper,hbs⟩ := ThreeBoundEndpoint40Seeds.seeds_of_periodic_upper SensitivityPublishing213303.periodic_upper m
  have hp : ThreeBoundEndpoint40Seeds.prefactor ≤ 10^69 := by decide +kernel
  exact ⟨n,f,hs,hupper.trans (Nat.mul_le_mul_right _ hp),hbs⟩
