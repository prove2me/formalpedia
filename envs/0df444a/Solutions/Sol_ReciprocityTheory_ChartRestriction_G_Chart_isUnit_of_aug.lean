-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.isUnit_of_aug
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:00.366653+00:00
-- url     : https://prove2.me/submissions/22e5c357-a750-4888-a52e-2ee8c9415594

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
import Definitions.Def_Lemmata_FirstBlockLemmaK_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_AlgChart
import Theorems.Thm_Bl_FirstBlockLemmaK_goal1


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (hJ : IsNilpotent (RingHom.ker aug))
    (a : A) (ha : IsUnit (aug a)) : IsUnit a := by
  exact @Bl.FirstBlockLemmaK.goal1 R _ A _ _ aug hJ a ha
end ReciprocityTheory.ChartRestriction.G.Chart
