-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Fr9__bi_l_af95f27a290e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:38:05.583421+00:00
-- url     : https://prove2.me/submissions/f966d135-76ef-46c8-b3b4-40d16d9971d4

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_bi_ff10c4ded450
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_zetaBarInv_commute_l0
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_comm_kapL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_io_fn_comm
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
theorem _root_.solution (h : IsFrame L f) (Y : ℂ) : io L.ζbi * f.l L Y = f.l L Y * io L.ζbi := by
  unfold FrameData.l
  rw [mul_add, add_mul, ← Wd11.io_mul, zetaBarInv_commute_l0, Wd11.io_mul, ← mul_assoc,
    (comm_kapL (fun g hg => io_fn_comm (mζbi L) hg)).eq, mul_assoc, mul_assoc, (h.ee_fn Y _ (mζbi L)).eq]
end Formalism.FourierDecayAlt.P.Fr9
