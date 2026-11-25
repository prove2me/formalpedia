-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.measurable_interpolatedWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:53:54.879217+00:00
-- url     : https://prove2.me/submissions/04575b48-c56a-4a3f-9c54-f9a993fe2f56

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AInterpSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseGenSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenMet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsBoundIteratedFDerivCompact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_measurable_coneMetric

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory
open scoped ContDiff
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {J : Type} [Fintype J] (m₀ m₁ : ConeMetric ℂ J)
    (h₀ : IsSmoothMetric m₀) (h₁ : IsSmoothMetric m₁) (t : ℝ) (n : ℕ) :
    Measurable (wgt (interp m₀ m₁ t) n) := by
  have hρ0 := measurable_coneMetric m₀ h₀
  have hρ1 := measurable_coneMetric m₁ h₁
  show Measurable fun z => ((m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t) ^ (2 * n))⁻¹
  exact (((hρ0.pow_const _).mul (hρ1.pow_const _)).pow_const _).inv
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
