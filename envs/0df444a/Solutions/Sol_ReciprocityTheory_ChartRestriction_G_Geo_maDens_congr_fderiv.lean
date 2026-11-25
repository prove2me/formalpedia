-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.maDens_congr_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:06:09.866285+00:00
-- url     : https://prove2.me/submissions/bc784bd7-a1b7-4837-bbbe-70dd310712d5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF

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
open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ i, fderiv ℝ (φ i) =ᶠ[𝓝 z] fderiv ℝ (ψ i)) :
    ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.AnForm.maDens ψ z := by
  have h2 : ∀ i, fderiv ℝ (fderiv ℝ (φ i)) z = fderiv ℝ (fderiv ℝ (ψ i)) z :=
    fun i => (h i).fderiv_eq
  unfold ReciprocityTheory.AnForm.maDens ReciprocityTheory.AnForm.hessC
  simp only [h2]
end ReciprocityTheory.ChartRestriction.G.Geo
