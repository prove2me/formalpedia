-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_evalOne_ratioMap_8be7c5deb8d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:07:33.040243+00:00
-- url     : https://prove2.me/submissions/f9cb7030-97e0-48b7-a7e1-494fac7558f3

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartConeComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ChartConeObjects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_evalOne_comp_ratioMap_fd9f5e3b1f68

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
variable {K : Type*} [Fintype K] {ι : K → Type*}
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution (i : (k : K) → ι k) (g : DehomRing i) : evalOne i (ratioMap i g) = g :=
  RingHom.congr_fun (evalOne_comp_ratioMap i) g
end GroundTheory.Heights₂.Heights.Targets
