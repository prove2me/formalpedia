-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.fp_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:24:10.327872+00:00
-- url     : https://prove2.me/submissions/f8211993-c749-49d8-95a6-2bdeb7816014

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ScalePowMono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_chart_smooth


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
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
variable [∀ s : S, Smooth (Gs G s).hom]
include G
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {s : S} (C : Chart (Gs G s)) : Algebra.FinitePresentation (Localization.Away s) Γ((Gs G s).left, C.U) := by
  haveI := chart_smooth (C := C)
  infer_instance
end ReciprocityTheory.ChartRestriction.G.Chart
