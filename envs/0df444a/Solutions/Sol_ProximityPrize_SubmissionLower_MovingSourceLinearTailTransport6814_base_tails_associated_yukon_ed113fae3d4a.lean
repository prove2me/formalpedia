-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceLinearTailTransport6814.base_tails_associated_yukon_ed113fae3d4a
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T22:44:29.79752+00:00
-- url     : https://prove2.me/submissions/22dd93c0-e8cd-4907-bf83-7f0a513c00bc




import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_18c42113a620563a44636057
import Definitions.Def_Yukon_4eb9e7e98149c44e25409e85
import Definitions.Def_Yukon_b9264d25766439028c5b06aa
set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.MovingSourceDenominatorChange6814
end MovingSourceDenominatorChange6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceFlowNumerator6814
end MovingSourceFlowNumerator6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN313
end RCN313
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN136
end RCN136
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN086
end RCN086
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceLinearTailTransport6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open RCN086 RCN136 RCN313
open MovingSourceFlowNumerator6814 MovingSourceDenominatorChange6814
variable {K Ω R : Type} [Field K] [Field Ω] [CommRing R] [IsDomain R]
local notation "Poly" => MvPolynomial (Fin 4) K
theorem _root_.solution
    (ev : Poly →+* R) (F H G : Poly) (n : ℕ) (hF : ev F=0)
    (hOld : IsUnit (ev (polyH K F))) (hNew : IsUnit (ev H))
    (hdiv : F∣H^(2*(n+2))*numerator K F (n+2)-
      (polyH K F)^(2*(n+2))*numerators H G (n+2)) :
    Associated (ev (RCN055.baseNumerator F n)) (ev (numerators H G (n+2)))  := by
  have hh := tails_associated ev F H G (n+2) hF hOld hNew hdiv
  rw [RCN055.numerator_eq_H_cube,map_mul,map_pow] at hh
  exact (associated_isUnit_mul_left_iff (hOld.pow 3)).mp hh
end
end MovingSourceLinearTailTransport6814
end SubmissionLower
end ProximityPrize
