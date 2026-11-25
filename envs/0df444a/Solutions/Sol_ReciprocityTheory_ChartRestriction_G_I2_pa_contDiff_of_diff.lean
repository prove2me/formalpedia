-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.pa_contDiff_of_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:56:34.221455+00:00
-- url     : https://prove2.me/submissions/6cfd2b5d-e9d7-4b81-a3bd-8d99e92a84f9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_contDiff_of_differentiable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex Metric
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {S : EuclideanSpace ℂ ι → ℂ} (hS : Differentiable ℂ S) :
    ContDiff ℂ (⊤ : ℕ∞) S := by
  classical
  let e : EuclideanSpace ℂ ι ≃L[ℂ] (Fin (Fintype.card ι) → ℂ) :=
    (EuclideanSpace.equiv ι ℂ).trans
      (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin ι).symm).toContinuousLinearEquiv
  have h1 : Differentiable ℂ (S ∘ e.symm) := hS.comp e.symm.differentiable
  have h2 : ContDiff ℂ (⊤ : ℕ∞) (S ∘ e.symm) := contDiff_of_differentiable h1
  have h3 := h2.comp e.contDiff
  convert h3 using 1
  funext v
  simp
end ReciprocityTheory.ChartRestriction.G.I2
