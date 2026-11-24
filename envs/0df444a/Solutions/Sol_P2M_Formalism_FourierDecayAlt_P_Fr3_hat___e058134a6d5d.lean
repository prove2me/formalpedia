-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Fr3_hat___e058134a6d5d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:25:25.771092+00:00
-- url     : https://prove2.me/submissions/ef87a142-bd6a-4234-8433-ca029d12de85

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_hat_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr3
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ} {L : LevelData A r} {f : FrameData S A}
namespace Formalism.FourierDecayAlt.P.Fr3
theorem _root_.solution (hf : IsFrame L f) {Y : ℂ} (hY : Y ∈ f.reg) : f.hatT Y 1 1 = io L.GG * f.x Y := by
  rw [hat_apply hY, hf.frame_τ Y hY, mul_assoc, hf.F_Fi, mul_one]
end Formalism.FourierDecayAlt.P.Fr3
