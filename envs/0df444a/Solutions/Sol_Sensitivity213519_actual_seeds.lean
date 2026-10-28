-- Prove2me | solution 1 for Sensitivity213519.actual_seeds
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T21:10:33.046234+00:00
-- url     : https://prove2.me/submissions/ac5ec051-73cc-4665-aa83-8e1fc9f6854b

import Definitions.Def_BS2_b3ba934b_Endpoint16Seeds
import Theorems.Thm_SensitivityPublishing213519_periodic_upper
set_option autoImplicit false

theorem solution : ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
  16^m ≤ OAI.Paper320.sensitivity f ∧
  OAI.Paper320.sensitivity f ≤ 10^69*31192129^m ∧
  (10007^4)^m ≤ OAI.Paper320.blockSensitivity f := by
  intro m
  obtain ⟨n,f,hs,hupper,hbs⟩ := ThreeBoundEndpoint16Seeds.seeds_of_periodic_upper SensitivityPublishing213519.periodic_upper m
  have hp : ThreeBoundEndpoint16Seeds.prefactor ≤ 10^69 := by decide +kernel
  exact ⟨n,f,hs,hupper.trans (Nat.mul_le_mul_right _ hp),hbs⟩
