-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.WholeSpacePowerCover6814.padded_native_fits_yukon_4968eef050de
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T08:17:16.02676+00:00
-- url     : https://prove2.me/submissions/f7576a72-10b1-4b3f-a10d-3da935d51e44


import Definitions.Def_Yukon_4f169e935332851cf48361a5



import Definitions.Def_Yukon_d5f981dd1b98d3409f17e3a0
set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedFlag
end SecondJetRelaxedFlag
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN095
end RCN095
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceNativeEnvelope6814
end MovingSourceNativeEnvelope6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.WholeSpacePowerBox6814
end WholeSpacePowerBox6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.WholeSpacePowerCover6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
open WholeSpacePowerBox6814 MovingSourceNativeEnvelope6814 RCN095 SecondJetRelaxedFlag
/-- Raising the middle envelope to the slope when necessary cannot create
an avoidance obligation: that whole native region fits already. -/
theorem _root_.solution (m s b t : ℕ)
    (hm : 0<m) (hs : 2≤s) (hms : m≤s) (hsb : 2*s≤b) (hbt : b≤t)
    (hb : copies3 m*b≤31) (ht : copies3 m*t≤995) :
    native m s b b t<3*272069082261391681*m  := by
  have heq := native_linear m s b b t hms hsb (by omega) hbt
  by_cases hm1 : m=1
  · subst m
    norm_num [copies3] at hb ht
    omega
  by_cases hm2 : m=2
  · subst m
    norm_num [copies3] at hb ht
    omega
  have hm3 : 3≤m := by omega
  have hq : copies3 m=1 := by
    unfold copies3
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [hq] at hb ht
  simp only [one_mul] at hb ht
  omega
end
end WholeSpacePowerCover6814
end SubmissionLower
end ProximityPrize
