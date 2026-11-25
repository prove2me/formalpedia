-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.contDiffOn_log_metric_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:02:26.619403+00:00
-- url     : https://prove2.me/submissions/f83c26d1-9731-415e-b25d-0db333ed1ff8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AInterpSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseGenSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenMet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsBoundIteratedFDerivCompact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_contDiffOn_of_analyticOnNhd

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
theorem _root_.solution {D : ℕ} {J : Type} [Fintype J] {P : Ideal (MvPolynomial J ℤ)}
    {U : Set (Fin D → ℂ)} {γ : (Fin D → ℂ) → J → ℂ} (m : ConeMetric ℂ J) (hm : IsSmoothMetric m)
    (hγ : IsParam P U γ) : ContDiffOn ℝ ∞ (fun y => Real.log (m.ρ (γ y))) U := by
  obtain ⟨_, hana, hpts, _⟩ := hγ
  have hγs : ContDiffOn ℝ ∞ γ U := contDiffOn_of_analyticOnNhd hana
  have hρ := hm.comp hγs (fun y hy => (hpts y hy).1)
  exact hρ.log (fun y hy => (m.pos _ (hpts y hy).1).ne')
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
