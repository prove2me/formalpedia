-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualPtsOnPlane_proof_e41a18cf842f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:22:21.735083+00:00
-- url     : https://prove2.me/submissions/4916782f-c84d-499c-8a62-05a635668373

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOnPlane
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_recover_spec_7ca4ae570c37
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualPointsOnPlane_agree_b46e2bd67bd3

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
open DualPointsOnPlane
namespace GroundTheory.Heights₂.Heights
namespace DualPtsOnPlane
theorem _root_.solution : DualPtsOnPlane.Statement := by
  intro K _ _ i F T _ _ b hb z hz
  obtain ⟨s0, hs0⟩ := hz.1 ()
  obtain ⟨p0, hp0⟩ : ∃ p, dualRecover b hb (fun t => z ⟨(), t⟩) p ≠ 0 := by
    by_contra hne
    simp only [ne_eq, not_exists, not_not] at hne
    exact hs0 ((recover_spec b hb (fun t => z ⟨(), t⟩) s0).trans (by simp [hne]))
  refine ⟨p0.1, fun τ hτ j => ?_⟩
  by_contra hne
  apply hτ
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 K))
  ext α
  exact agree b hb z hz α (τ, j) p0 hne hp0
end DualPtsOnPlane
end GroundTheory.Heights₂.Heights
