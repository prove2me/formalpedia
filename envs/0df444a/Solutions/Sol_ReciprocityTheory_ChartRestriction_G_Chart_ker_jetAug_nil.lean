-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.ker_jetAug_nil
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:59.07161+00:00
-- url     : https://prove2.me/submissions/8a50b133-e405-4f46-ac18-f985457d0004

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow

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
theorem _root_.solution (κ : Type) (m : ℕ) : IsNilpotent (RingHom.ker (jetAug R κ m)) :=
  ⟨m + 1, by rw [ker_jetAug_pow, Ideal.zero_eq_bot]⟩
end ReciprocityTheory.ChartRestriction.G.Chart
