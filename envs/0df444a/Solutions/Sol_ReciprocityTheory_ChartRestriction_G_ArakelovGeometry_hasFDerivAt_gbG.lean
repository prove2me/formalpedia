-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.hasFDerivAt_gbG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:51:44.084998+00:00
-- url     : https://prove2.me/submissions/a702c748-86b7-4978-add9-4df0eddb1b21

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbBil_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbG_eq

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
theorem _root_.solution (y : Fin D → ℂ) : HasFDerivAt gbG (2 • gbBil D y) y := by
  have h := (gbBil D).hasFDerivAt_of_bilinear (hasFDerivAt_id y) (hasFDerivAt_id y)
  have h2 := h.const_add 1
  have hfun : (fun y' => 1 + gbBil D (id y') (id y')) = gbG := funext fun y' => (gbG_eq y').symm
  rw [hfun] at h2
  refine h2.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun u => ?_
  simp
  rw [gbBil_comm u y]
  ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
