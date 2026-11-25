-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_embComp_lin_2d6da04684f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:15:56.208347+00:00
-- url     : https://prove2.me/submissions/85ad7510-c20e-41f5-a5ca-d600aeaccf47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjPtsOnPlane
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_embComp_recon_1ea4fa5bd66c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_lin_eq_3c8f669433de

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
theorem _root_.solution (α : 𝓞 K) (Z : ProjIdx K i → ℂ) (τ : K →+* ℂ) :
    embComp τ (lin α Z) = τ (α : K) • embComp τ Z := by
  have h : lin α Z = fun q : ProjIdx K i =>
      ∑ σ : K →+* ℂ, σ (integralBasis K q.1) * (fun σ j => σ (α : K) * embComp σ Z j) σ q.2 :=
    funext fun q => lin_eq α Z q
  rw [h]
  exact embComp_recon (fun σ j => σ (α : K) * embComp σ Z j) τ
end GroundTheory.Heights₂.Heights.ProjectivePointsOnPlane
