-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Fr8_star__bi_58cd25344a8d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:37:46.292692+00:00
-- url     : https://prove2.me/submissions/a2905ccc-96b1-42fd-b1f2-e8d5682af84b

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_star_inv
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr8_star__b_8b8b591566b9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr8
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Fr8
theorem _root_.solution {L : LevelData A r} (h : IsStarLevel L) : star L.ζbi = L.ζi := star_inv L.ζb_ζbi (star_ζb h) L.ζ_ζi
end Formalism.FourierDecayAlt.P.Fr8
