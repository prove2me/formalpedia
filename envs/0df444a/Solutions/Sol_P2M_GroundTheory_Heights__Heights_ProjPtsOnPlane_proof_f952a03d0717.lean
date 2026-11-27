-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjPtsOnPlane_proof_f952a03d0717
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:08:53.006127+00:00
-- url     : https://prove2.me/submissions/a80cfc35-03ab-4db1-9f45-cbc9300857fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjPtsOnPlane
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_agree_9a060891ac52

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
open ProjectivePointsOnPlane
namespace GroundTheory.Heights₂.Heights
namespace ProjPtsOnPlane
theorem _root_.solution : ProjPtsOnPlane.Statement := by
  intro K _ _ i z hz
  obtain ⟨⟨m0, j0⟩, hq0⟩ := hz.1 ()
  obtain ⟨σ, j, hσ⟩ : ∃ (σ : K →+* ℂ) (j : Fin i), embComp σ (fun q => z ⟨(), q⟩) j ≠ 0 := by
    by_contra hne
    simp only [ne_eq, not_exists, not_not] at hne
    exact hq0 ((sum_emb_embComp (fun q => z ⟨(), q⟩) m0 j0).symm.trans (by simp [hne]))
  refine ⟨σ, fun τ hτ => ?_⟩
  funext l
  by_contra hne
  apply hτ
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 K))
  ext α
  exact agree z hz α τ σ l j hne hσ
end ProjPtsOnPlane
end GroundTheory.Heights₂.Heights
