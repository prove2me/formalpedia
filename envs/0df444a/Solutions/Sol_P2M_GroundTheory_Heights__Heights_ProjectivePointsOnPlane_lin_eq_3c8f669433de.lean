-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_lin_eq_3c8f669433de
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:51.708697+00:00
-- url     : https://prove2.me/submissions/8b092b36-89f3-48e0-86a9-be297eb08897

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjPtsOnPlane
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_mulMat_sum_04dda0bf4bd3

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
theorem _root_.solution (α : 𝓞 K) (Z : ProjIdx K i → ℂ) (q : ProjIdx K i) :
    lin α Z q = ∑ σ : K →+* ℂ, σ (integralBasis K q.1) * (σ (α : K) * embComp σ Z q.2) := by
  calc lin α Z q
      = ∑ n, ∑ σ : K →+* ℂ, (mulMat α q.1 n : ℂ) * (σ (integralBasis K n) * embComp σ Z q.2) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← sum_emb_embComp Z n q.2, Finset.mul_sum]
    _ = ∑ σ : K →+* ℂ, (∑ n, (mulMat α q.1 n : ℂ) * σ (integralBasis K n)) * embComp σ Z q.2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun n _ => by ring
    _ = _ := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        have h := congrArg σ (mulMat_sum α q.1)
        simp only [map_sum, map_mul, map_intCast] at h
        rw [h]
        ring
end GroundTheory.Heights₂.Heights.ProjectivePointsOnPlane
