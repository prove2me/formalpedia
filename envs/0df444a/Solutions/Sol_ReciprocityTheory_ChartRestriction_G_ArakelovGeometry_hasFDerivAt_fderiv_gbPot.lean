-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.hasFDerivAt_fderiv_gbPot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:39:44.290929+00:00
-- url     : https://prove2.me/submissions/54d28a93-dbfa-4c95-ac73-77df67ae94fb

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_fderiv_gbPot

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
theorem _root_.solution (y : Fin D → ℂ) :
    HasFDerivAt (fderiv ℝ gbPot)
      ((gbG y)⁻¹ • gbBil D + ((-((gbG y) ^ 2)⁻¹) • (2 • gbBil D y)).smulRight (gbBil D y)) y := by
  rw [fderiv_gbPot]
  have hi : HasFDerivAt (fun y => (gbG y)⁻¹) ((-((gbG y) ^ 2)⁻¹) • (2 • gbBil D y)) y := by
    have := (hasDerivAt_inv (gbG_pos y).ne').comp_hasFDerivAt y (hasFDerivAt_gbG y)
    exact this
  exact hi.smul (gbBil D).hasFDerivAt
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
