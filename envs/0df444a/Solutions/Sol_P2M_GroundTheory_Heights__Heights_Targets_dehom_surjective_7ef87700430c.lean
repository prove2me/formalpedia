-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_dehom_surjective_7ef87700430c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:26.031313+00:00
-- url     : https://prove2.me/submissions/612fc954-db79-43a5-bb0b-317fc3c2e45f

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
omit [Fintype K]
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution (i : (k : K) → ι k) : Function.Surjective (dehom i) :=
  Ideal.Quotient.mk_surjective
end GroundTheory.Heights₂.Heights.Targets
