-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceLinearTailTransport6814.proper_delay_iff_yukon_f459559191ea
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T22:44:35.426122+00:00
-- url     : https://prove2.me/submissions/a3c17877-6146-46f0-87cf-d1c687e84395




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
theorem _root_.solution
    (phi : Polynomial K →+* Ω) (hphi : Function.Injective phi)
    (ev : MvPolynomial (Fin 3) Ω →+* R) (F H G : Poly)
    (hF : ev (surfaceMap phi F)=0)
    (hOld : IsUnit (ev (surfaceMap phi (polyH K F)))) (hNew : IsUnit (ev (surfaceMap phi H)))
    (hdiv : ∀ n, F∣H^(2*n)*numerator K F n-(polyH K F)^(2*n)*numerators H G n)
    (start delay : ℕ) :
    ((∀ j<delay, ¬IsUnit (ev (globalTailCut phi F (start+j)))) ∧
      IsUnit (ev (globalTailCut phi F (start+delay)))) ↔
    ((∀ j<delay, ¬IsUnit (ev (surfaceMap phi (numerators H G (start+j))))) ∧
      IsUnit (ev (surfaceMap phi (numerators H G (start+delay)))))  := by
  have hu (n : ℕ) : IsUnit (ev (globalTailCut phi F n)) ↔
      IsUnit (ev (surfaceMap phi (numerators H G n))) :=
    (global_tails_associated phi hphi ev F H G n hF hOld hNew (hdiv n)).isUnit_iff
  simp_rw [hu]
end
end MovingSourceLinearTailTransport6814
end SubmissionLower
end ProximityPrize
