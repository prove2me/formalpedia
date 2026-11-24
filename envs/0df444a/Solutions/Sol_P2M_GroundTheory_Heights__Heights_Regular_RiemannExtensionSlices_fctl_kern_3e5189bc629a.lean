-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_fctl_kern_3e5189bc629a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:47.645084+00:00
-- url     : https://prove2.me/submissions/2a76e66a-1087-4d6e-9812-ef119bb8a8bf

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PRiemannExtensionSlices
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_cubeProj_of_mem
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_kern_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Complex Metric MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.Osgood
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
namespace GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
theorem _root_.solution {n : ℕ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) (f : (Fin n → ℂ) → ℂ)
    (hz : z ∈ ball c r) :
    fctl c r f (kern c r z) = ∯ ζ in T(c, fun _ => r), (∏ i, (ζ i - z i)⁻¹) * f ζ := by
  unfold fctl torusIntegral
  refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  simp only [jac, kern_apply hr hz, cubeProj_of_mem hθ, smul_eq_mul]
  ring
end GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
