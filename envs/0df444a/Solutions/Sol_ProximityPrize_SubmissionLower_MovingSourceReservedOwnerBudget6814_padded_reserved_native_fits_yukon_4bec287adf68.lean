-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceReservedOwnerBudget6814.padded_reserved_native_fits_yukon_4bec287adf68
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T13:35:16.862917+00:00
-- url     : https://prove2.me/submissions/1de89e5c-2b33-44d4-ba96-c957330e78be

import Mathlib
import Definitions.Def_Yukon_d5f981dd1b98d3409f17e3a0
import Definitions.Def_Yukon_4f169e935332851cf48361a5
import Definitions.Def_Yukon_f6fa1fddb6f3331fee11343a

set_option autoImplicit false

open ProximityPrize.SubmissionLower.WholeSpacePowerBox6814 ProximityPrize.SubmissionLower.WholeSpacePowerCover6814 ProximityPrize.SubmissionLower.MovingSourceNativeEnvelope6814 ProximityPrize.SubmissionLower.RCN095 ProximityPrize.SubmissionLower.SecondJetRelaxedFlag ProximityPrize.SubmissionLower.MovingSourceReservedOwnerBudget6814 in
theorem solution (m s b t : ℕ)
    (hm : 0 < m) (hs : 2 ≤ s) (hms : m ≤ s) (hsb : 2*s ≤ b) (hbt : b ≤ t)
    (hb : copies3 m*b ≤ 31) (ht : copies3 m*t ≤ 995) :
    native m s b b t < 3*mainAllowance*m  := by
  have hlin := native_linear m s b b t hms hsb le_rfl hbt
  have hA : mainAllowance = 271949082261391681 := rfl
  rw [hA]
  rcases Nat.lt_or_ge m 3 with h3 | h3
  · interval_cases m
    · have hc : copies3 1 = 3 := by decide
      rw [hc] at hb ht
      omega
    · have hc : copies3 2 = 2 := by decide
      rw [hc] at hb ht
      omega
  · have hc : 1 ≤ copies3 m := copies3_pos m hm
    have hb' : b ≤ 31 := le_trans (Nat.le_mul_of_pos_left b hc) hb
    have ht' : t ≤ 995 := le_trans (Nat.le_mul_of_pos_left t hc) ht
    omega
