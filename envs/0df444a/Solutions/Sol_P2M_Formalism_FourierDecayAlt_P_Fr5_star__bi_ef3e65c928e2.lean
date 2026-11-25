-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Fr5_star__bi_ef3e65c928e2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:38:15.663625+00:00
-- url     : https://prove2.me/submissions/6dc9bcfd-8a24-4bcd-b7d6-e08de8f0c2ac

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2OfFourEntries
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr5_star__i_3a44bc578970

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr5
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Fr5
theorem _root_.solution {L : LevelData A r} (h : IsStarLevel L) : star L.ζbi = L.ζi := by
  rw [← star_ζi h, star_star]
end Formalism.FourierDecayAlt.P.Fr5
