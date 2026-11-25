-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity.eSec_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:24:04.449337+00:00
-- url     : https://prove2.me/submissions/806e7ff2-4e82-4967-b549-db223aed486f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_PairProp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ResEqOfResEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_eSec_pG

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
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιG : RingAct G O) (e : ℕ) (a : O)
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
theorem _root_.solution (χ : D.toPre.X) :
    eSec (thickObj R I e G) ≫ (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left =
      ((Over.map (thick R I e)).map η[thickObj R I e G] ≫ toUnit _ ≫ D.toPre.c χ).left ≫
        (zz D.toPre.P.A).left := by
  show ((Over.map (thick R I e)).map η[thickObj R I e G]).left ≫ _ = _
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  rw [comp_lift, eSec_pG, comp_lift, Category.comp_id, ← Category.assoc _ (toUnit D.toPre.P.A),
    toUnit_unique (_ ≫ toUnit D.toPre.P.A) (toUnit _)]
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
