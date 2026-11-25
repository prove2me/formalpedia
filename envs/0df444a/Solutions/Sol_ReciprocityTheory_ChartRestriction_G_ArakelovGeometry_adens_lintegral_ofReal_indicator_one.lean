-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_lintegral_ofReal_indicator_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:40:02.848114+00:00
-- url     : https://prove2.me/submissions/16660e63-397a-4227-a814-3c605b5d85c2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStA

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology
variable {J : Type} [Fintype J] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {α : Type*} [MeasurableSpace α] (ν : Measure α) {S C : Set α}
    (hS : MeasurableSet S) :
    ∫⁻ z in C, ENNReal.ofReal (S.indicator (fun _ => (1 : ℝ)) z) ∂ν = ν (S ∩ C) := by
  have hfun : (fun z => ENNReal.ofReal (S.indicator (fun _ => (1 : ℝ)) z)) =
      S.indicator (fun _ => (1 : ENNReal)) := by
    funext z
    by_cases hz : z ∈ S <;> simp [hz]
  rw [hfun, lintegral_indicator_const hS, one_mul, Measure.restrict_apply hS]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
