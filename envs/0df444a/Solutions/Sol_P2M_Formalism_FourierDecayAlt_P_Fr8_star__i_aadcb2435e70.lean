-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Fr8_star__i_aadcb2435e70
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:38:04.593528+00:00
-- url     : https://prove2.me/submissions/bc9885b4-1319-4cb5-bda7-5939bc1afbb3

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_star_inv

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
theorem _root_.solution {L : LevelData A r} (h : IsStarLevel L) : star L.ζi = L.ζbi := by
  obtain ⟨h1, -, -⟩ := h
  exact star_inv L.ζ_ζi h1 L.ζb_ζbi
end Formalism.FourierDecayAlt.P.Fr8
