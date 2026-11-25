-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.cab_contDiff_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:45:51.455747+00:00
-- url     : https://prove2.me/submissions/6cee93a5-6abe-4ee2-a104-72311801898c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelA
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
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {F : W → ℂ} (hF : Differentiable ℂ F) : ContDiff ℂ (⊤ : WithTop ℕ∞) F := by
  let e : W ≃L[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    (Module.finBasis ℂ W).equivFun.toContinuousLinearEquiv
  have h1 : Differentiable ℂ (F ∘ e.symm) := hF.comp e.symm.differentiable
  have h3 : ContDiff ℂ (⊤ : WithTop ℕ∞) (F ∘ e.symm) := contDiff_of_differentiable h1
  have : F = (F ∘ e.symm) ∘ e := by ext x; simp
  rw [this]
  exact h3.comp e.contDiff
end ReciprocityTheory.ChartRestriction.G.I2
