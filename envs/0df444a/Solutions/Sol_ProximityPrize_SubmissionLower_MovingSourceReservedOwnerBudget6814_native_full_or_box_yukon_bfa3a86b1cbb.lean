-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceReservedOwnerBudget6814.native_full_or_box_yukon_bfa3a86b1cbb
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T09:07:35.528809+00:00
-- url     : https://prove2.me/submissions/8670fd71-8db7-46ec-9e17-c18c9e5653a2

import Definitions.Def_Yukon_d5f981dd1b98d3409f17e3a0



import Theorems.Thm_ProximityPrize_SubmissionLower_MovingSourceReservedOwnerBudget6814_reserved_failure_has_box_yukon_94d0bb2bc364
import Definitions.Def_Yukon_4f169e935332851cf48361a5
import Definitions.Def_Yukon_f6fa1fddb6f3331fee11343a
set_option backward.isDefEq.respectTransparency.types false
private abbrev ProximityPrize.SubmissionLower.MovingSourceReservedOwnerBudget6814.reserved_failure_has_box := @ProximityPrize.SubmissionLower.MovingSourceReservedOwnerBudget6814.reserved_failure_has_box_yukon_94d0bb2bc364
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
namespace ProximityPrize.SubmissionLower.WholeSpacePowerCover6814
end WholeSpacePowerCover6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.WholeSpacePowerBox6814
end WholeSpacePowerBox6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceReservedOwnerBudget6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 15000
open WholeSpacePowerBox6814 WholeSpacePowerCover6814 MovingSourceNativeEnvelope6814
open RCN095 SecondJetRelaxedFlag
theorem _root_.solution (m s b u t : ℕ)
    (hm : 0<m) (hs : 2≤s) (hms : m≤s) (hsb : 2*s≤b) (hbu : b≤u) (hut : u≤t)
    (hb : copies3 m*b≤31) (hu : copies3 m*u≤98) (ht : copies3 m*t≤995)
    (hex : 3≤m → 5≤s) :
    native m s b u t+3*m*auxiliaryCharge m s b u t<3*272069082261391681*m ∨
      HasBox (copies3 m) b u t  := by
  by_cases hfit : native m s b u t<3*mainAllowance*m
  · left
    have hq := copies3_pos m hm
    have hb' := Nat.mul_le_mul_right b hq
    have hu' := Nat.mul_le_mul_right u hq
    have ht' := Nat.mul_le_mul_right t hq
    exact reserved_native_fits m s b u t hm hsb (by omega) (by omega) (by omega) hfit
  · exact Or.inr (reserved_failure_has_box m s b u t hm hs hms hsb hbu hut hb hu ht hex (by omega))
end
end MovingSourceReservedOwnerBudget6814
end SubmissionLower
end ProximityPrize
