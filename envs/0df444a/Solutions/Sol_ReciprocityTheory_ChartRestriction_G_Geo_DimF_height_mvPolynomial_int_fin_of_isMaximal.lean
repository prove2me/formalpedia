-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_mvPolynomial_int_fin_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:51:35.5938+00:00
-- url     : https://prove2.me/submissions/be340e1b-a03b-4bfc-bc2d-8293a8ceb84b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_IsCMOfIsRegularLocalRing
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_RingKrullDimLocalizationQuotientEqHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_height_int_of_isMaximal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_height_polynomial_of_isMaximal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_int_isJacobsonRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.DimF
namespace ReciprocityTheory.ChartRestriction.G.Geo.DimF
theorem _root_.solution :
    ∀ (n : ℕ) (M : Ideal (MvPolynomial (Fin n) ℤ)), M.IsMaximal → M.height = n + 1
  | 0, M, hM => by
    let e := MvPolynomial.isEmptyRingEquiv ℤ (Fin 0)
    have hM' : (M.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    rw [← e.height_map M, height_int_of_isMaximal _ hM']
    simp
  | n + 1, M, hM => by
    have := int_isJacobsonRing
    let e := (MvPolynomial.finSuccEquiv ℤ n).toRingEquiv
    have hM' : (M.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    rw [← e.height_map M, height_polynomial_of_isMaximal
      (solution n) _ hM']
    push_cast
    ring
end ReciprocityTheory.ChartRestriction.G.Geo.DimF
