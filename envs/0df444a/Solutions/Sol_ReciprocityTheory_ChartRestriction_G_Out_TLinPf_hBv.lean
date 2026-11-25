-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.hBv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:24:25.203609+00:00
-- url     : https://prove2.me/submissions/8626fed6-4f22-4650-990d-e1e03aa288b2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_CanonGenIsGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_OrbitMapConjSmulZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_eB

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
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))
include hO
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf
theorem _root_.solution : φB U ιG e a χ =
    ![(padd D.toPre.P.A ((U.gt e).pG ≫ ιD.onB.act a) (xc e χ (G := G))).left,
      (xc e χ (G := G)).left, ((U.gt e).pG ≫ ιD.onB.act a).left,
      (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ η[D.toPre.P.A]).left] := by
  funext k
  rw [eB U ιD ιG e a χ hO k]
  fin_cases k <;> rfl
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
