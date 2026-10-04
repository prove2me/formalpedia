-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceLinearTailTransport6814.global_tail_orders_yukon_f2aa47322833
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T22:44:31.919488+00:00
-- url     : https://prove2.me/submissions/cbfe1bcc-6b7e-4942-bf13-b2a5121de402




import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
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
theorem _root_.solution [IsDiscreteValuationRing R]
    (phi : Polynomial K →+* Ω) (hphi : Function.Injective phi)
    (ev : MvPolynomial (Fin 3) Ω →+* R) (F H G : Poly) (n : ℕ)
    (hF : ev (surfaceMap phi F)=0)
    (hOld : IsUnit (ev (surfaceMap phi (polyH K F)))) (hNew : IsUnit (ev (surfaceMap phi H)))
    (hdiv : F∣H^(2*n)*numerator K F n-(polyH K F)^(2*n)*numerators H G n) :
    IsDiscreteValuationRing.addVal R (ev (globalTailCut phi F n))=
      IsDiscreteValuationRing.addVal R (ev (surfaceMap phi (numerators H G n)))  := (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr
    (global_tails_associated phi hphi ev F H G n hF hOld hNew hdiv)
end
end MovingSourceLinearTailTransport6814
end SubmissionLower
end ProximityPrize
