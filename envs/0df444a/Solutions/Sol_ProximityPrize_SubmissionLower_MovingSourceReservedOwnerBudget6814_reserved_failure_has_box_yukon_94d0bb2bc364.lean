-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceReservedOwnerBudget6814.reserved_failure_has_box_yukon_94d0bb2bc364
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T08:31:51.866886+00:00
-- url     : https://prove2.me/submissions/2da7e8ac-63ae-47c4-9b61-38c160f2dfee

import Definitions.Def_Yukon_d5f981dd1b98d3409f17e3a0



import Definitions.Def_Yukon_4f169e935332851cf48361a5
import Definitions.Def_Yukon_f6fa1fddb6f3331fee11343a
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
    (hex : 3≤m → 5≤s)
    (hfail : 3*mainAllowance*m≤native m s b u t) :
    HasBox (copies3 m) b u t  := by
  have heq := native_linear m s b u t hms hsb hbu hut
  unfold mainAllowance at hfail
  by_cases hm1 : m=1
  · subst m
    norm_num [copies3] at hb hu ht ⊢
    apply cover1 b u t <;> omega
  by_cases hm2 : m=2
  · subst m
    norm_num [copies3] at hb hu ht ⊢
    apply cover2 b u t <;> omega
  have hm3 : 3≤m := by omega
  have hq : copies3 m=1 := by
    unfold copies3
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [hq] at hb hu ht ⊢
  simp only [one_mul] at hb hu ht
  have hs5 := hex hm3
  apply cover3 b u t <;> omega
end
end MovingSourceReservedOwnerBudget6814
end SubmissionLower
end ProximityPrize
