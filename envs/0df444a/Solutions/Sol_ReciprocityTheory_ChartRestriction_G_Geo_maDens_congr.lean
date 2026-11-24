-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.maDens_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:53.309878+00:00
-- url     : https://prove2.me/submissions/113d9fa5-c94e-4d65-95d8-4472346bbf8a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA

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
open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology MeasureTheory
open scoped ContDiff
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ i, φ i =ᶠ[𝓝 z] ψ i) : ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.AnForm.maDens ψ z := by
  have hH : ∀ i, ReciprocityTheory.AnForm.hessC (φ i) z = ReciprocityTheory.AnForm.hessC (ψ i) z := by
    intro i
    have h2 : fderiv ℝ (fderiv ℝ (φ i)) z = fderiv ℝ (fderiv ℝ (ψ i)) z :=
      ((h i).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    unfold ReciprocityTheory.AnForm.hessC
    rw [h2]
  simp only [ReciprocityTheory.AnForm.maDens, hH]
end ReciprocityTheory.ChartRestriction.G.Geo
