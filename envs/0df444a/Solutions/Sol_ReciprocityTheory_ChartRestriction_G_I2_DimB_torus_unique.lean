-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimB.torus_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:07:53.209376+00:00
-- url     : https://prove2.me/submissions/757ab835-2814-4640-afaf-ddd4c35d80cb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Complex
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.DimB
variable {k : ℕ}
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_11
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_13
attribute [local instance] ReciprocityTheory.ChartRestriction.G.I2.DimB._p2m_local_instance_697ec7c02f_16
namespace ReciprocityTheory.ChartRestriction.G.I2.DimB
theorem _root_.solution (D : C(UnitAddTorus (Fin k), ℂ))
    (h : ∀ n, UnitAddTorus.mFourierCoeff D n = 0) : D = 0 := by
  have hinj := (UnitAddTorus.mFourierBasis (d := Fin k)).repr.injective
  have h1 := @hinj (ContinuousMap.toLp 2 _ ℂ D) 0 (by
    rw [map_zero]
    refine lp.ext (funext fun n => ?_)
    rw [UnitAddTorus.mFourierBasis_repr, UnitAddTorus.mFourierCoeff_toLp, h]
    rfl)
  exact ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) (E := ℂ) _ (h1.trans (map_zero _).symm)
end ReciprocityTheory.ChartRestriction.G.I2.DimB
