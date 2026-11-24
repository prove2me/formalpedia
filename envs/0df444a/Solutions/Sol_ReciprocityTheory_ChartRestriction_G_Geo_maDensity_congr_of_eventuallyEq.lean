-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.maDensity_congr_of_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:26.833803+00:00
-- url     : https://prove2.me/submissions/65b153b9-ba1e-49e9-91a9-8c04510ce634

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : ∀ j, φ j =ᶠ[𝓝 y] ψ j) : maDensity φ y = maDensity ψ y := by
  have h2 : ∀ j, fderiv ℝ (fderiv ℝ (φ j)) y = fderiv ℝ (fderiv ℝ (ψ j)) y := fun j =>
    Filter.EventuallyEq.fderiv_eq (show fderiv ℝ (φ j) =ᶠ[𝓝 y] fderiv ℝ (ψ j) from
      (h j).eventuallyEq_nhds.mono fun _ h' => h'.fderiv_eq)
  have hH : ∀ k, cxHessian (φ k) y = cxHessian (ψ k) y := by
    intro k
    unfold cxHessian
    rw [h2 k]
  simp only [maDensity, hH]
end ReciprocityTheory.ChartRestriction.G.Geo
