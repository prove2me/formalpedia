-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isBounded_ballProd_f634cf668f3e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:45.963369+00:00
-- url     : https://prove2.me/submissions/c160c3cc-05d4-42a3-865b-23c2a2a1dbda

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_norm_le_of_hermNorm_lt_7188355ead98

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
theorem _root_.solution (h : HermNorm n) (k : ℕ) : Bornology.IsBounded (ballProd h k) := by
  have hR : 0 ≤ ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine (Metric.isBounded_closedBall (x := (0 : Fin k × Fin n → ℂ))
    (r := ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖)).subset fun u hu => ?_
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]
  rintro ⟨i, j⟩
  exact norm_le_of_hermNorm_lt h (hu i) j
end GroundTheory.Heights₂.Heights
