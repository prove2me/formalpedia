-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Fr10_tri_mul__7132e1048a78
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:38:14.233882+00:00
-- url     : https://prove2.me/submissions/ee443a4a-2e82-4055-bc53-c079466b79ba

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommuteInvLeft
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinusLetterFrameOfData
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_io_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_io_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_diag_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_diag_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr10
open Formalism.FourierDecayAlt.P.Wd1
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
variable {r : ℕ} (L : LevelData A r) (f : FrameData S A)
namespace Formalism.FourierDecayAlt.P.Fr10
theorem _root_.solution (m : SlopeTestRemainingChoices S A) :
    (!![1, 0; -m, io L.GGi] * !![io L.ζb, 0; 0, io L.ζ]) *
      (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * m, io L.GG]) = (1 : M2 (SlopeTestRemainingChoices S A)) := by
  have h1 : (!![1, 0; -m, io L.GGi] * !![1, 0; io L.GG * m, io L.GG] : M2 (SlopeTestRemainingChoices S A)) = 1 := by
    rw [Matrix.mul_fin_two, ← diag_one]
    simp [← mul_assoc, ← io_mul, L.GGi_GG, io_one]
  calc _ = !![1, 0; -m, io L.GGi] * ((!![io L.ζb, 0; 0, io L.ζ] * !![io L.ζbi, 0; 0, io L.ζi]) *
        !![1, 0; io L.GG * m, io L.GG]) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [diag_mul, ← io_mul, ← io_mul, L.ζb_ζbi, L.ζ_ζi, io_one, diag_one, Matrix.one_mul, h1]
end Formalism.FourierDecayAlt.P.Fr10
