-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mahler_C_02c18ff6a9ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:02:34.009366+00:00
-- url     : https://prove2.me/submissions/d8f3d795-501d-4b7a-9beb-fcc6b8df46c4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sphereMean_const_6bf8a279dfbc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField
noncomputable section
open Matrix
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (h : HermNorm n) (k : ℕ) (z : ℂ) :
    mahler h k (C z : MvPolynomial (Fin k × Fin n) ℂ) = Real.log ‖z‖ := by
  unfold mahler
  simp only [eval_C]
  exact sphereMean_const h k _
end GroundTheory.Heights₂.Heights
