-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.dualLift_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:26:29.596157+00:00
-- url     : https://prove2.me/submissions/c83ccc8f-218b-4d16-a8ac-154e605096a6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_IsUnivChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {n : ℕ} {c c' : Fin n → R} (h : dualLift (R := R) c = dualLift c') : c = c' := by
  funext j
  have := congrArg TrivSqZeroExt.snd (AlgHom.congr_fun h (zR 1 j))
  rwa [dualLift_zR, dualLift_zR, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_inr] at this
end ReciprocityTheory.ChartRestriction.G.Chart
