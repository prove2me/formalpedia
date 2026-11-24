-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaM_tendsto_antider
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:51.254293+00:00
-- url     : https://prove2.me/submissions/25d3c637-989b-44ae-a0ed-8a034059af63

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
theorem _root_.solution {b : ℝ} (_hb : 0 < b) (j : ℕ) :
    Tendsto (fun r : ℝ => -(1 / (2 * ((j : ℝ) + 1))) * ((b + r ^ 2) ^ (j + 1))⁻¹) atTop (𝓝 0) := by
  have h1 : Tendsto (fun r : ℝ => b + r ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
  have h2 : Tendsto (fun r : ℝ => (b + r ^ 2) ^ (j + 1)) atTop atTop :=
    (tendsto_pow_atTop (Nat.succ_ne_zero j)).comp h1
  simpa using (tendsto_inv_atTop_zero.comp h2).const_mul (-(1 / (2 * ((j : ℝ) + 1))))
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
