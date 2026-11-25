-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_T0_isUnit_of_val_eq_zero__c03558623f11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:52:50.977446+00:00
-- url     : https://prove2.me/submissions/8b381633-c750-4a2e-b67b-3a42b3b13683

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValExists
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValLeIffDivMem
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussIndepOfLeTrdeg
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntegralClosureRankAndResidueTrdegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentResidueOfIsUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_mem_valuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {E : Type} [Field E] (v : AddValuation E (WithTop ℤ)) {z : E}
    (h : z ∈ vRing v) (hz : v z = 0) : IsUnit (⟨z, h⟩ : vRing v) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [AddValuation.map_zero] at hz
    exact WithTop.top_ne_coe hz
  have hinv : z⁻¹ ∈ vRing v := by
    rw [mem_valuationRing, AddValuation.map_inv, hz, neg_zero]
  exact IsUnit.of_mul_eq_one (⟨z⁻¹, hinv⟩ : vRing v) (Subtype.ext (mul_inv_cancel₀ hz0))
end ReciprocityTheory.ChartRestriction.G.T0
