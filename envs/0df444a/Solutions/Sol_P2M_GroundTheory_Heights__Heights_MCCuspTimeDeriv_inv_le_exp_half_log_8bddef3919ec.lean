-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCCuspTimeDeriv_inv_le_exp_half_log_8bddef3919ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:04.371854+00:00
-- url     : https://prove2.me/submissions/d866d9d4-83d5-4478-96cf-651368fa72f3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspTimeDeriv

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
open GroundTheory.Heights₂.Heights.MCCuspTimeDeriv
namespace GroundTheory.Heights₂.Heights.MCCuspTimeDeriv
theorem _root_.solution {x : ℝ} (hx : 0 < x) :
    x⁻¹ ≤ Real.exp (Real.log (x ^ 2)⁻¹ / 2) := by
  have h : Real.log (x ^ 2)⁻¹ / 2 = Real.log x⁻¹ := by
    rw [Real.log_inv, Real.log_inv, Real.log_pow]; push_cast; ring
  rw [h, Real.exp_log (inv_pos.mpr hx)]
end GroundTheory.Heights₂.Heights.MCCuspTimeDeriv
