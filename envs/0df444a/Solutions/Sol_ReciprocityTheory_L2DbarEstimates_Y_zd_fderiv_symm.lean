-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.zd_fderiv_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:42:22.155734+00:00
-- url     : https://prove2.me/submissions/8a7c09de-ef8a-46b3-a46a-bedee201eb1d

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IndCount
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZeroDimA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
open scoped ContDiff
noncomputable section
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {k : ℕ} {g : E → ContinuousMultilinearMap ℂ (fun _ : Fin k => E) F}
    {y : E} (h : ∀ᶠ z in 𝓝 y, ∀ (τ : Equiv.Perm (Fin k)) (w : Fin k → E), g z (w ∘ τ) = g z w)
    (τ : Equiv.Perm (Fin k)) (u : E) (w : Fin k → E) :
    fderiv ℂ g y u (w ∘ τ) = fderiv ℂ g y u w := by
  by_cases hg : DifferentiableAt ℂ g y
  · have hev : (fun z => g z (w ∘ τ)) =ᶠ[𝓝 y] fun z => g z w := h.mono fun z hz => hz τ w
    rw [← fderiv_continuousMultilinear_apply_const_apply hg (w ∘ τ) u,
      ← fderiv_continuousMultilinear_apply_const_apply hg w u, hev.fderiv_eq]
  · simp [fderiv_zero_of_not_differentiableAt hg]
end ReciprocityTheory.L2DbarEstimates.Y
