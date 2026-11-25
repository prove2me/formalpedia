-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Fr9__iGG_l_e5b3e6892b8a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:38:06.229827+00:00
-- url     : https://prove2.me/submissions/4b8cf281-bcda-4521-8cff-8d18e8bae182

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_i_e9f2f11151ee
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_mG
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_io_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_zetaInv_GG_conj_l0
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_comm_kapL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_io_fn_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_kapL_tz
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
theorem _root_.solution (h : IsFrame L f) (Y : ℂ) :
    io L.ζi * io L.GG * f.l L Y = (f.l L Y + kapL L * tz L) * (io L.ζi * io L.GG) := by
  unfold FrameData.l
  have c : Commute (io L.ζi * io L.GG : SlopeTestRemainingChoices S A) (kapL L * f.ee Y) :=
    ((comm_kapL (fun g hg => io_fn_comm (mζi L) hg)).mul_right (h.ee_fn Y _ (mζi L)).symm).mul_left
      ((comm_kapL (fun g hg => io_fn_comm (mG L) hg)).mul_right (h.ee_fn Y _ (mG L)).symm)
  rw [mul_add, c.eq, kapL_tz, ← Wd11.io_mul, ← Wd11.io_mul, zetaInv_GG_conj_l0, Wd11.io_mul, io_add, add_mul, add_mul,
    add_mul]
  abel
end Formalism.FourierDecayAlt.P.Fr9
