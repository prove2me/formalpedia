-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_continuous_hermNorm_group_3228c37461df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:25:53.940586+00:00
-- url     : https://prove2.me/submissions/566aea87-2907-4581-aaf8-ac7e592e9cbd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup

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
theorem _root_.solution (h : HermNorm n) {k : ℕ} (i : Fin k) :
    Continuous fun u : Fin k × Fin n → ℂ => h.norm (fun j => u (i, j)) := by
  simp only [HermNorm.norm, Matrix.mulVec, dotProduct]
  fun_prop
end GroundTheory.Heights₂.Heights
