-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift.hL_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:37:56.352463+00:00
-- url     : https://prove2.me/submissions/fe1e2d9d-49a9-4043-a9ed-dcc69b1f795b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteDimensionalOfLiftY
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OffBaseSubstitution
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FractionFieldVariableLift_hL_C
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FractionFieldVariableLift_hL_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
open ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift
variable {K : Type} [Field K] {Ω : Type} [Field Ω] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift
theorem _root_.solution (p : MvPolynomial {v : TVar D N // v.1 ≠ 0} K) :
    hL K D N (MvPolynomial.rename Subtype.val p) = MvPolynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.rename_C, hL_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p n hp => rw [map_mul, map_mul, hp, MvPolynomial.rename_X, hL_X, dif_neg n.2, map_mul]
end ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift
