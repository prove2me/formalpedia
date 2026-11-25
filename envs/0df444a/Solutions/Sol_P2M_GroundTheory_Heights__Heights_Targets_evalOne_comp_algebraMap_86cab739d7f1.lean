-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_evalOne_comp_algebraMap_86cab739d7f1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:10:04.14171+00:00
-- url     : https://prove2.me/submissions/f30f8e30-eb19-41d0-b59d-be21c6bc7285

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartConeComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ChartConeObjects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_evalOne_algebraMap_0b540b7cbc3b

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
theorem _root_.solution (i : (k : K) → ι k) :
    (evalOne i).comp (algebraMap _ (ConeRing i)) = (dehom i : MvPolynomial (Σ k, ι k) ℂ →+* DehomRing i) :=
  RingHom.ext (evalOne_algebraMap i)
end GroundTheory.Heights₂.Heights.Targets
