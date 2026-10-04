-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceClearing6814.movingCut_zero_iff_yukon_df2f6c75f260
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T00:19:44.34492+00:00
-- url     : https://prove2.me/submissions/1f023b55-a6ce-4a34-9e1b-13110e825341




import Theorems.Thm_ProximityPrize_SubmissionLower_MovingSourceClearing6814_movingCut_value_yukon_ad183332c771
import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561
import Definitions.Def_Yukon_91e99a7c9682f8cc19028ba7
import Definitions.Def_Yukon_ca06e00072579899a61b0098
set_option backward.isDefEq.respectTransparency.types false
private abbrev ProximityPrize.SubmissionLower.MovingSourceClearing6814.movingCut_value := @ProximityPrize.SubmissionLower.MovingSourceClearing6814.movingCut_value_yukon_ad183332c771
namespace ProximityPrize.SubmissionLower.SecondJetClearedHelper
end SecondJetClearedHelper
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.SecondJetCoefficients
end SecondJetCoefficients
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN207
end RCN207
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN136
end RCN136
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN095
end RCN095
end SubmissionLower
end ProximityPrize
namespace MvPolynomial
end MvPolynomial
namespace ProximityPrize.SubmissionLower.MovingSourceClearing6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
open MvPolynomial RCN095 RCN136 RCN207
open SecondJetCoefficients SecondJetClearedHelper
section Surface
variable {K E : Type*} [Field K] [Field E]
local notation "Poly3" => MvPolynomial (Fin 3) E
theorem _root_.solution {L : Type*} [Field L]
    (phi : Polynomial K →+* E) (ev : Poly3 →+* L)
    (P : WholeSpaceCube6814.Poly (K := K)) (s : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (H G Q A : Poly3) (target : E) (sigma : L)
    (hH : ev H≠0) (hN : ev (movingEquation H G Q A target)=0)
    (hsigma : ev (2*H)*sigma=ev G) (hA : ev (2*A)≠0) :
    ev (movingCut phi P s Q A target)=0 ↔
      ((asS P).map (ev.comp (surfaceMap phi))).eval sigma=0  := by
  rw [movingCut_value phi ev P s hS H G Q A target sigma hH hN hsigma]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero s hA))
end Surface
end
end MovingSourceClearing6814
end SubmissionLower
end ProximityPrize
