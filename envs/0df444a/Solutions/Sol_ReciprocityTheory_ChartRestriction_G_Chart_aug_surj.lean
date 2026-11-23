-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.aug_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:18.750487+00:00
-- url     : https://prove2.me/submissions/98c72696-2f3a-45bf-ad64-d7e6912831f6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
import Definitions.Def_Lemmata_FirstBlockLemmaK_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_AlgChart

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
theorem _root_.solution {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) : Function.Surjective aug :=
  fun r => ⟨algebraMap R A r, by rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]⟩
end ReciprocityTheory.ChartRestriction.G.Chart
