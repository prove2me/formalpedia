-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TubeEuclMass_proof_70c60c19c863
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:12:12.362214+00:00
-- url     : https://prove2.me/submissions/e5a75622-7ef1-4aad-8ec5-f95ae0321286

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeEuclMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeCollarMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeEuclMass

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
open MvPolynomial MeasureTheory Matrix ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace TubeEuclMass
theorem _root_.solution (hC : TubeCollarMass.Statement) (hD : TubeDeepMass.Statement) :
    TubeEuclMass.Statement := by
  intro n d J A P R hJ hdim hA hP
  have hS : {y : Fin (d + 1) → ℂ | logAbsSq P y < -Real.exp 1} =
      {y | -Real.exp 1 ≤ logAbsSq P y}ᶜ := by
    ext y
    simp [not_le]
  have h := (hC n d J A P R hJ hdim hA hP).add (hD n d J A P R hJ hdim hA hP)
  rw [hS, Set.indicator_self_add_compl] at h
  exact h
end TubeEuclMass
end GroundTheory.Heights₂.Heights
