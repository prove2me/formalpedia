-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.hasFDerivAt_gbPot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:10:38.809832+00:00
-- url     : https://prove2.me/submissions/79690391-09d0-4670-92b6-10ddbb4b11d6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbG_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_hasFDerivAt_gbG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbPot_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open MeasureTheory Set Filter Topology
open scoped ENNReal
open ReciprocityTheory.ChartRestriction.G.Geo
variable {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (y : Fin D → ℂ) : HasFDerivAt gbPot ((gbG y)⁻¹ • gbBil D y) y := by
  have h := HasFDerivAt.const_mul (HasFDerivAt.log (hasFDerivAt_gbG y) (gbG_pos y).ne') (1 / 2 : ℝ)
  have hfun : (fun y' : Fin D → ℂ => (1 / 2 : ℝ) * Real.log (gbG y')) = gbPot :=
    funext fun y' => by rw [gbPot_eq]; ring
  rw [hfun] at h
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun u => ?_
  simp
  ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
