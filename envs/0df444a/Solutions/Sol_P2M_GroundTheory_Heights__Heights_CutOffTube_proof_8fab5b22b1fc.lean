-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CutOffTube_proof_8fab5b22b1fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:56:15.803841+00:00
-- url     : https://prove2.me/submissions/6a61e2eb-1415-4438-8ae9-957eeed292f5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffTube
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeEuclMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffTube
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_measurable_tubeDens_109588edc399
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_tubeDens_nonneg_84f1fc7d5825

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
open MvPolynomial MeasureTheory Filter Matrix ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace CutOffTube
theorem _root_.solution (hC : TubeFormCompare.Statement) (hE : TubeEuclMass.Statement) :
    CutOffTube.Statement := by
  intro n d J A P R φ hJ hdim hA hP hφ
  obtain ⟨C, hCle⟩ := hC n d J A P R φ hJ hdim hA hφ
  refine Integrable.mono' ((hE n d J A P R hJ hdim hA hP).const_mul C)
    (measurable_tubeDens hA P R φ).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (tubeDens_nonneg J A P R φ y)]
  exact hCle y
end CutOffTube
end GroundTheory.Heights₂.Heights
