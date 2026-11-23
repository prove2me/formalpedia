-- Prove2me | solution 1 for ReciprocityTheory.AnForm.levi_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:17.107814+00:00
-- url     : https://prove2.me/submissions/f7636106-2bf3-47bb-90d7-4c78f9fa1471

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open Filter Topology
open scoped ContDiff
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
namespace ReciprocityTheory.AnForm
theorem _root_.solution {φ ψ : (ι → ℂ) → ℝ} {z : ι → ℂ} (h : φ =ᶠ[𝓝 z] ψ) (w : ι → ℂ) :
    levi φ z w = levi ψ z w := by
  have h2 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ ψ := h.eventuallyEq_nhds.mono fun y hy => hy.fderiv_eq
  unfold levi
  rw [h2.fderiv_eq]
end ReciprocityTheory.AnForm
