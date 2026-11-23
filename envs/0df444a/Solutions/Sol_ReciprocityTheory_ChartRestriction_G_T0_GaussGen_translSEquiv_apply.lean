-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:36.195803+00:00
-- url     : https://prove2.me/submissions/3c007482-4dc2-4ad1-9b49-aac456f16dcc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtLeafSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_MapDomainMemOfDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_TranslSEquivApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.GaussGen
open MvPolynomial NumberField BlockPoly
variable {Ω : Type} [Field Ω] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.GaussGen
theorem _root_.solution (j₀ : Fin (N + 1)) (a : Fin (N + 1) → Ω)
    (g : MvPolynomial (SVar D N) Ω) : translSEquiv j₀ a g = translS j₀ a g := rfl
end ReciprocityTheory.ChartRestriction.G.T0.GaussGen
