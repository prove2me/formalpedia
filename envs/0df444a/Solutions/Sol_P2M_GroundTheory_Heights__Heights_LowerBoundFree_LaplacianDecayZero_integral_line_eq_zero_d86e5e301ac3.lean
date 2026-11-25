-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_LaplacianDecayZero_integral_line_eq_zero_d86e5e301ac3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:04:21.907072+00:00
-- url     : https://prove2.me/submissions/def999d1-2f88-42e3-8239-be2b5f703d48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsLaplacianDecayZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PLaplacianDecayZero

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open InnerProductSpace Laplacian MeasureTheory Filter Topology
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
namespace LaplacianDecayZero
theorem _root_.solution (v : ℂ → ℝ)
    (hdiff : Differentiable ℝ (fderiv ℝ v))
    (hlim : Tendsto (fderiv ℝ v) (cocompact ℂ) (𝓝 0)) (w e : ℂ) (he : ‖e‖ = 1) :
    ∫ t : ℝ, fderiv ℝ (fderiv ℝ v) (w + (t : ℂ) * e) e e = 0 := by
  have hγd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => w + (s : ℂ) * e) e t := by
    intro t
    have := (((hasDerivAt_id t).ofReal_comp).mul_const e).const_add w
    simpa using this
  have hF : ∀ t : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ v (w + (s : ℂ) * e) e)
      (fderiv ℝ (fderiv ℝ v) (w + (t : ℂ) * e) e e) t := by
    intro t
    have h1 := ((hdiff (w + (t : ℂ) * e)).hasFDerivAt).comp_hasDerivAt t (hγd t)
    have h2 := (ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp_hasDerivAt t h1
    exact h2
  have hiso : Isometry (fun s : ℝ => w + (s : ℂ) * e) := by
    refine Isometry.of_dist_eq fun s t => ?_
    rw [dist_eq_norm, dist_eq_norm,
      show w + (s : ℂ) * e - (w + (t : ℂ) * e) = ((s - t : ℝ) : ℂ) * e by push_cast; ring,
      norm_mul, he, mul_one, Complex.norm_real]
  have hcoc : Tendsto (fun s : ℝ => w + (s : ℂ) * e) (cocompact ℝ) (cocompact ℂ) :=
    hiso.isClosedEmbedding.tendsto_cocompact
  have hlim' : Tendsto (fun s : ℝ => fderiv ℝ v (w + (s : ℂ) * e) e) (cocompact ℝ) (𝓝 0) := by
    have := ((ContinuousLinearMap.apply ℝ ℝ e).continuous.tendsto 0).comp (hlim.comp hcoc)
    exact this
  by_cases hint : Integrable (fun t : ℝ => fderiv ℝ (fderiv ℝ v) (w + (t : ℂ) * e) e e)
  · have := integral_of_hasDerivAt_of_tendsto hF hint (hlim'.mono_left atBot_le_cocompact)
      (hlim'.mono_left atTop_le_cocompact)
    simpa using this
  · exact integral_undef hint
end LaplacianDecayZero
end GroundTheory.Heights₂.Heights.LowerBoundFree
