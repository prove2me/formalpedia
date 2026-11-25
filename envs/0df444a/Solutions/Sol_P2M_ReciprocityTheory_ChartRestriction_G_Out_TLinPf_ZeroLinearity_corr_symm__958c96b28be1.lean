-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_corr_symm__958c96b28be1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:53:17.039376+00:00
-- url     : https://prove2.me/submissions/9a7192c8-3f18-47e8-a862-000aff69cbd5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_PairProp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ResEqOfResEq
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_res_eq_of_res_eq__709669c04f21

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.TLinPf
open Semi
open ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
variable {X Y Z W : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
theorem _root_.solution {K' : Type} [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)}
    {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : LB.Gen.Corr L φ ε φ' ε' t t') : LB.Gen.Corr L φ' ε' φ ε t' t := by
  intro j j' hj hj' hjj
  exact (res_eq_of_res_eq' _ _ _ _
    (h j' j hj' hj fun k k' hk => (hjj k' k hk.symm).symm)).symm
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
