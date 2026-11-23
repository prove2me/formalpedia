-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.GaussGen.Pimg_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:02.973738+00:00
-- url     : https://prove2.me/submissions/b8e19b36-9d86-4a68-a715-b3a4b7016272

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
theorem _root_.solution (j₀ : Fin (N + 1)) (x : Fin N → Ω) (i : Fin (D + 1)) :
    Pimg j₀ x (i, j₀) =
      if i = 0 then X (Sum.inl ()) else -∑ k, X (Sum.inr (i, k)) * C (x k) := by
  unfold Pimg
  exact Fin.insertNth_apply_same (α := fun _ => MvPolynomial (SVar D N) Ω) j₀ _ _
end ReciprocityTheory.ChartRestriction.G.T0.GaussGen
