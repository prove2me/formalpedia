-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_comp_toPoly_dea409fd7470
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:36:32.33647+00:00
-- url     : https://prove2.me/submissions/ec1b8881-9536-45e1-acf0-a64f0532c40a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_toPoly_toChart_75e66e3dda35

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.ChartDomain
variable {D : Type} [CommRing D] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n)
namespace GroundTheory.Heights₂.Heights.Vertical.ChartDomain
theorem _root_.solution : (fromPoly Q j e).comp (toPoly Q j e) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (xj Q j e))
  apply Ideal.Quotient.ringHom_ext
  exact fromPoly_toPoly_toChart Q j
end GroundTheory.Heights₂.Heights.Vertical.ChartDomain
