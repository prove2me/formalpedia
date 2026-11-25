-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RadialPrimitive_primitive_contDiff_d60144194930
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:53.887937+00:00
-- url     : https://prove2.me/submissions/4e322cdf-69f8-4924-b678-01c6eb590f2a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRadialPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRadialPrimitive

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
open MeasureTheory
open scoped ContDiff
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace RadialPrimitive
theorem _root_.solution (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (c : ℝ) :
    ContDiff ℝ ∞ (fun t => ∫ τ in c..t, f τ) ∧ deriv (fun t => ∫ τ in c..t, f τ) = f := by
  have hd : deriv (fun t => ∫ τ in c..t, f τ) = f :=
    funext fun t => hf.continuous.deriv_integral f c t
  refine ⟨contDiff_infty_iff_deriv.2 ⟨fun t => ?_, by rw [hd]; exact hf⟩, hd⟩
  exact (hf.continuous.integral_hasStrictDerivAt c t).hasDerivAt.differentiableAt
end RadialPrimitive
end GroundTheory.Heights₂.Heights
