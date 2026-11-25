-- Prove2me | solution 1 for P2M_GlobalTheory_ChartUniv_spMap_id__b39f24ee8cf8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:50:14.179101+00:00
-- url     : https://prove2.me/submissions/f6a600b8-4c0e-4efc-aa5f-fa3381661b52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsUniversalChartOfFormalGroupChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left


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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChartUniv
open ReciprocityTheory.ChartRestriction.G.Chart
variable {R : Type} [CommRing R]
namespace GlobalTheory.ChartUniv
theorem _root_.solution (A : Type) [CommRing A] [Algebra R A] : spMap (R₀ := R) (AlgHom.id R A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  rw [spMap_left]
  exact Spec.map_id _
end GlobalTheory.ChartUniv
