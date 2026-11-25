-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.hA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:05:26.207092+00:00
-- url     : https://prove2.me/submissions/fbc23668-6462-430b-bfd9-86da12af2a44

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_CanonGenIsGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_OrbitMapConjSmulZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_orbitMap_conj_smul_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_orbitMap_conj_smul_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_orbitMap_conj_smul_two
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_selfLieBasisVector
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_eR

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
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf
theorem _root_.solution : φA U ιD e a χ = Sum.elim
    ![(padd D.toPre.P.A (U.gt e).pG (xc e χ (G := G) ≫ ιD.onB.act (star a))).left,
      (xc e χ (G := G) ≫ ιD.onB.act (star a)).left, (U.gt e).pG.left,
      (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ η[D.toPre.P.A]).left]
    ![(padd D.toPre.P.A (xc e χ (G := G) ≫ ιD.onB.act (star a)) (U.gt e).pG).left,
      (xc e χ (G := G) ≫ ιD.onB.act (star a)).left, (U.gt e).pG.left,
      (padd D.toPre.P.A (xc e χ (G := G)) ((U.gt e).pG ≫ ιD.onB.act a)).left,
      (xc e χ (G := G)).left, ((U.gt e).pG ≫ ιD.onB.act a).left] := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
    eR (e := e) (ιD.onB.act (star a)) (ιD.onB.act a) (xc e χ (G := G)) (U.gt e).pG
  funext k
  rcases k with k | k
  · fin_cases k
    · exact orbitMap_conj_smul_zero U ιD e a χ
    · exact orbitMap_conj_smul_one U ιD e a χ
    · exact orbitMap_conj_smul_two U e a χ
    · exact selfLieBasisVector U e a χ
  · fin_cases k
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
