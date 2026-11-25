-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.leviZ_wd_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:28:37.848819+00:00
-- url     : https://prove2.me/submissions/8e7eac47-1d52-4419-8844-3ae0a1a1f0f6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LeviZCoordChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (n : ℕ) (j l : Fin n) (y : V n) :
    wd n j (fun w : V n => w l) y = if j = l then 1 else 0 := by
  have hL : fderiv ℝ (fun w : V n => w l) y =
      ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ) :=
    ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).hasFDerivAt.restrictScalars ℝ).fderiv
  unfold wd
  rw [hL]
  by_cases h : j = l
  · subst h
    simp [bas, EuclideanSpace.single_apply, Complex.I_mul_I]
  · simp [bas, EuclideanSpace.single_apply, h, Ne.symm h]
end ReciprocityTheory.L2DbarEstimates.F
