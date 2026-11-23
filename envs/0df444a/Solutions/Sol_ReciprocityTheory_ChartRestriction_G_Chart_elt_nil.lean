-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.elt_nil
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:16:46.559049+00:00
-- url     : https://prove2.me/submissions/d5e9ff92-bfb8-4fe3-bf35-07dd32d33a51

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
theorem _root_.solution {A : Type} [CommRing A] (J : Ideal A) (hJ : IsNilpotent J) : ∀ a ∈ J, IsNilpotent a := by
  obtain ⟨N, hN⟩ := hJ
  intro a ha
  refine ⟨N, ?_⟩
  have := Ideal.pow_mem_pow ha N
  rw [hN, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  exact this
end ReciprocityTheory.ChartRestriction.G.Chart
