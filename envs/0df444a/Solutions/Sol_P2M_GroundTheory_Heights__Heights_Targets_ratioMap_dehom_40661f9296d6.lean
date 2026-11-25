-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ratioMap_dehom_40661f9296d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:29:48.3466+00:00
-- url     : https://prove2.me/submissions/e8964bd1-1d47-4e61-8d06-79a3335666af

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartConeComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ChartConeObjects

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
theorem _root_.solution (i : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ) :
    ratioMap i (dehom i f) = coneRatio i f :=
  Ideal.Quotient.lift_mk _ _ _
end GroundTheory.Heights₂.Heights.Targets
