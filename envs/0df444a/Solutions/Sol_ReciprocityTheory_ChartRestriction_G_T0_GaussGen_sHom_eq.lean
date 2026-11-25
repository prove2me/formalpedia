-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.GaussGen.sHom_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:37:18.030684+00:00
-- url     : https://prove2.me/submissions/49964145-3503-4510-9e34-b3435f2d9ce0

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
theorem _root_.solution {K : Type} [Field K] [Algebra K Ω] (j₀ : Fin (N + 1)) (x : Fin N → Ω)
    (y : MvPolynomial (TVar D N) K) :
    sHom j₀ x y = algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (aeval (Pimg j₀ x) y) := by
  show aeval (sImg j₀ x) y = _
  rw [← MvPolynomial.aeval_algebraMap_apply]
  rfl
end ReciprocityTheory.ChartRestriction.G.T0.GaussGen
