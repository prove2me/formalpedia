-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaM_integrableOn_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:43:35.338896+00:00
-- url     : https://prove2.me/submissions/c314bd08-bede-4a98-88b1-0f5c0f609393

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gaM_hasDerivAt_antider
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gaM_tendsto_antider

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
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {b : ℝ} (hb : 0 < b) (j : ℕ) :
    IntegrableOn (fun r : ℝ => r * ((b + r ^ 2) ^ (j + 2))⁻¹) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun x _ => gaM_hasDerivAt_antider hb j x)
    (fun x hx => by have : 0 < b + x ^ 2 := by positivity
                    exact mul_nonneg (le_of_lt hx) (by positivity))
    (gaM_tendsto_antider hb j)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
