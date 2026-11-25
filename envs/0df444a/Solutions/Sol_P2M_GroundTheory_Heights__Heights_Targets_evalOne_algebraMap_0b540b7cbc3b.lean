-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_evalOne_algebraMap_0b540b7cbc3b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:00:58.347711+00:00
-- url     : https://prove2.me/submissions/0bb51608-db11-4b5d-9366-0db647e15521

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
    evalOne i (algebraMap _ (ConeRing i) f) = dehom i f :=
  IsLocalization.lift_eq _ _
end GroundTheory.Heights₂.Heights.Targets
