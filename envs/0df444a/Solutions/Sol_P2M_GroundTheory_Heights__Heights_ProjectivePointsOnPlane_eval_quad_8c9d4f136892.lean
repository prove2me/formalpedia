-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_eval_quad_8c9d4f136892
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:50.66822+00:00
-- url     : https://prove2.me/submissions/03b98125-4721-4d73-bca3-bdde8c5ac9b9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjPtsOnPlane

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
open GroundTheory.Heights₂.Heights.ProjectivePointsOnPlane
variable {K : Type} [Field K] [NumberField K] {i : ℕ}
namespace GroundTheory.Heights₂.Heights.ProjectivePointsOnPlane
theorem _root_.solution (z : (Σ _ : Unit, ProjIdx K i) → ℂ) (α : 𝓞 K) (p q : ProjIdx K i) :
    eval z (map (Int.castRingHom ℂ) (quad α p q)) =
      z ⟨(), p⟩ * lin α (fun r => z ⟨(), r⟩) q - lin α (fun r => z ⟨(), r⟩) p * z ⟨(), q⟩ := by
  simp [quad, lform, lin]
end GroundTheory.Heights₂.Heights.ProjectivePointsOnPlane
