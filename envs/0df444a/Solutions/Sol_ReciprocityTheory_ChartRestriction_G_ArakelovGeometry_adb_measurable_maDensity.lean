-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adb_measurable_maDensity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:51:30.477707+00:00
-- url     : https://prove2.me/submissions/056daf9a-e8f2-41bd-bf41-b79587ad5711

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStBA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adb_measurable_cxHessian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Topology
open scoped ComplexOrder
variable {κ : Type} [Fintype κ] {D : ℕ}
variable {P : Ideal (MRing (GlobalTheory κ))} {Ψ : (((k : Unit) → GlobalTheory κ k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)}
  {U : Set (Fin D → ℂ)} {γ : (Fin D → ℂ) → Ix κ → ℂ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (φ : Fin D → (Fin D → ℂ) → ℝ) : Measurable (maDensity φ) := by
  have hcx : ∀ k i j, Measurable fun z => cxHessian (φ k) z i j := fun k i j =>
    adb_measurable_cxHessian (φ k) i j
  unfold maDensity mixedDisc
  simp only [Matrix.det_apply, Matrix.sum_apply]
  refine measurable_const.mul (Complex.measurable_re.comp (measurable_const.mul
    (Finset.measurable_sum _ fun S _ => measurable_const.mul
      (Finset.measurable_sum _ fun σ _ => (Finset.measurable_prod _ fun i _ =>
        Finset.measurable_sum _ fun k _ => hcx k _ _).const_smul _))))
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
