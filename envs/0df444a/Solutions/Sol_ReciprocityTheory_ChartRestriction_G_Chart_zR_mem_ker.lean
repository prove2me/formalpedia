-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.zR_mem_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:44.229365+00:00
-- url     : https://prove2.me/submissions/42c6d36b-0565-4530-abc9-2acb250edc0a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR

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
open MvPolynomial
variable (R : Type) [CommRing R]
variable {R}
variable (R)
variable {R}
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {κ : Type} (m : ℕ) (j : κ) : zR (R := R) m j ∈ RingHom.ker (jetAug R κ m) :=
  jetAug_zR m j
end ReciprocityTheory.ChartRestriction.G.Chart
