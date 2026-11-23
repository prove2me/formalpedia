-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.jetZero_zR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:25.00611+00:00
-- url     : https://prove2.me/submissions/9556061e-8af4-46ad-ae58-d82d64a02b03

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
theorem _root_.solution (n m : ℕ) (j : Fin n) : jetZeroR R (Fin n) m (zR m j) = 0 := by
  show Ideal.Quotient.mk _ (MvPolynomial.X j) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
  exact Ideal.subset_span ⟨j, rfl⟩
end ReciprocityTheory.ChartRestriction.G.Chart
