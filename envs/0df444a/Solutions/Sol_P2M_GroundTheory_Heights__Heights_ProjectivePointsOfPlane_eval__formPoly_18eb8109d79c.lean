-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectivePointsOfPlane_eval__formPoly_18eb8109d79c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:47:50.688824+00:00
-- url     : https://prove2.me/submissions/6ca8f286-d8d4-4f9c-b3a1-1cc303663fab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjPtsOfPlane

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ProjectivePointsOfPlane
variable {K : Type} [Field K] [NumberField K] {i : ℕ}
namespace GroundTheory.Heights₂.Heights.ProjectivePointsOfPlane
theorem _root_.solution (σ : K →+* ℂ) (v : Fin i → ℂ) (p : Σ _ : Unit, ProjIdx K i) :
    eval₂Hom σ v (formPoly p) = projPlanePt σ v p := by
  simp [formPoly, projPlanePt]
end GroundTheory.Heights₂.Heights.ProjectivePointsOfPlane
