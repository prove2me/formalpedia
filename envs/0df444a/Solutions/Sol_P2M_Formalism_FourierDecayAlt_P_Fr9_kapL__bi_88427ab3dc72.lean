-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Fr9_kapL__bi_88427ab3dc72
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:38:06.98297+00:00
-- url     : https://prove2.me/submissions/eb927d47-a70e-48ac-b634-0b323153a15e

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_zc
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_i_e9f2f11151ee
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_bi_ff10c4ded450
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_mGi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_io_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr9
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ}
variable {L : LevelData A r} {f : FrameData S A}
namespace Formalism.FourierDecayAlt.P.Fr9
theorem _root_.solution : (kapL L : SlopeTestRemainingChoices S A) * io L.ζbi = io L.ζi * io L.GGi := by
  unfold kapL
  rw [← Wd11.io_mul, ← Wd11.io_mul]
  congr 1
  rw [mul_assoc, mul_assoc, zc L (mGi L) (mζbi L), ← mul_assoc L.ζi, zc L (mζi L) (mζbi L), mul_assoc,
    ← mul_assoc, L.ζb_ζbi, one_mul]
end Formalism.FourierDecayAlt.P.Fr9
