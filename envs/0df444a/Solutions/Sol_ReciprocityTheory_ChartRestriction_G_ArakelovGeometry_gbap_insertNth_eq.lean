-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_insertNth_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:50:28.246116+00:00
-- url     : https://prove2.me/submissions/618a73a7-8eae-48bd-b55c-7fc37e148b89

import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_ExistsAnalyticGraphChartMvPolynomial
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {D : ℕ} (k : Fin (D + 1)) (a : ℂ) (b : Fin D → ℂ) (w : Fin (D + 1) → ℂ)
    (hk : w k = a) (hb : ∀ i, w (k.succAbove i) = b i) : Fin.insertNth k a b = w := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove k j with rfl | ⟨i, rfl⟩
  · simp [hk]
  · simp [hb]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
