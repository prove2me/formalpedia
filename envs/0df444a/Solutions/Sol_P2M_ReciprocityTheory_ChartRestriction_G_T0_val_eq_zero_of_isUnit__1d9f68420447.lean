-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_T0_val_eq_zero_of_isUnit__1d9f68420447
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:52:58.81585+00:00
-- url     : https://prove2.me/submissions/3f5a3ea3-49ca-4b8f-9aab-94f7bb1b87eb

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
    (h : z ∈ vRing v) (hu : IsUnit (⟨z, h⟩ : vRing v)) : v z = 0 := by
  obtain ⟨u, hu⟩ := hu
  have hmul : z * ((↑u⁻¹ : vRing v) : E) = 1 := by
    have h1 := u.mul_inv
    rw [hu] at h1
    exact congrArg Subtype.val h1
  have hsum : v z + v ((↑u⁻¹ : vRing v) : E) = 0 := by
    rw [← AddValuation.map_mul, hmul, AddValuation.map_one]
  exact ((add_eq_zero_iff_of_nonneg ((mem_valuationRing v z).mp h)
    ((mem_valuationRing v _).mp (↑u⁻¹ : vRing v).2)).mp hsum).1
end ReciprocityTheory.ChartRestriction.G.T0
