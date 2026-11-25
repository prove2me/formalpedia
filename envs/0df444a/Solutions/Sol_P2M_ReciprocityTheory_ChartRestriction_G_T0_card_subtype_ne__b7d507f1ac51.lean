-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_T0_card_subtype_ne__b7d507f1ac51
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:52:44.901471+00:00
-- url     : https://prove2.me/submissions/49933206-6323-414b-a586-39fa4585ec36

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentResidueOfIsUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValAlgebraMapEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {σ : Type} [Fintype σ] [DecidableEq σ] (e0 : σ) :
    Fintype.card {e // e ≠ e0} = Fintype.card σ - 1 := by
  first
  | rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  | simp [Fintype.card_subtype_compl]
end ReciprocityTheory.ChartRestriction.G.T0
