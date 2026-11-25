-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_ph_fderiv__05db1d76e71f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:38:15.234919+00:00
-- url     : https://prove2.me/submissions/2384bd83-a30e-46e9-bacc-8eb9021e3f1a

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_P_fderiv
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_ph_fderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (s : ℝ) (x v : E) :
    fderiv ℝ (fun y => quad φ y + s * E_P φ y) x v = fderiv ℝ φ x v - (1 - s) * fderiv ℝ (E_P φ) x v := by
  rw [E_ph_fderiv hφ, E_P_fderiv hφ]
  simp
  ring
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
