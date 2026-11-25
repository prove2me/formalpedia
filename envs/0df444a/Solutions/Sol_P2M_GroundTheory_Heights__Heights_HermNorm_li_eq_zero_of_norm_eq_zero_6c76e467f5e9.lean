-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermNorm_li_eq_zero_of_norm_eq_zero_6c76e467f5e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:38:28.362914+00:00
-- url     : https://prove2.me/submissions/951c85dc-4d87-495c-93a5-256ef83a8b8e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_exists_coord_le_93e1a2c1b1f2

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
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.HermNorm
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.HermNorm
theorem _root_.solution (h : HermNorm n) (v : Fin n → ℂ) (hv : h.norm v = 0) : v = 0 := by
  obtain ⟨C, -, hC⟩ := h.li_exists_coord_le
  funext j
  have := hC v j
  rw [hv, mul_zero] at this
  exact norm_le_zero_iff.mp this
end GroundTheory.Heights₂.Heights.HermNorm
