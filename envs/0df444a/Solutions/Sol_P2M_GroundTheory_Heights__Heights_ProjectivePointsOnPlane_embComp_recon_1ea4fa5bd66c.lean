-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjectivePointsOnPlane_embComp_recon_1ea4fa5bd66c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:47:32.678315+00:00
-- url     : https://prove2.me/submissions/5360f1d4-f840-48e3-b7b2-0bddb81d5fd8

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
open scoped Classical
namespace GroundTheory.Heights₂.Heights.ProjectivePointsOnPlane
theorem _root_.solution (u : (K →+* ℂ) → Fin i → ℂ) (τ : K →+* ℂ) :
    embComp τ (fun q : ProjIdx K i => ∑ σ : K →+* ℂ, σ (integralBasis K q.1) * u σ q.2) = u τ := by
  set b := canonicalEmbedding.latticeBasis K
  have hd : ∀ σ : K →+* ℂ, ∑ m, b.repr (Pi.single τ 1) m * σ (integralBasis K m) =
      if σ = τ then 1 else 0 := by
    intro σ
    have h := congrFun (b.sum_repr (Pi.single τ 1)) σ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, b, canonicalEmbedding.latticeBasis_apply,
      canonicalEmbedding.apply_at, Pi.single_apply] at h
    exact h
  funext j
  calc embComp τ (fun q : ProjIdx K i => ∑ σ : K →+* ℂ, σ (integralBasis K q.1) * u σ q.2) j
      = ∑ m, ∑ σ : K →+* ℂ, b.repr (Pi.single τ 1) m * (σ (integralBasis K m) * u σ j) := by
        simp only [embComp, Finset.mul_sum]; rfl
    _ = ∑ σ : K →+* ℂ, (∑ m, b.repr (Pi.single τ 1) m * σ (integralBasis K m)) * u σ j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun m _ => by ring
    _ = u τ j := by
        rw [Finset.sum_congr rfl fun σ _ => congrArg (· * u σ j) (hd σ)]
        simp
end GroundTheory.Heights₂.Heights.ProjectivePointsOnPlane
