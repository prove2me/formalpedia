-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.hsub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:59.013828+00:00
-- url     : https://prove2.me/submissions/4504e05c-e21c-410e-8f09-c7c3ac63a2df

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_CanonGenIsGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_OrbitMapConjSmulZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_padd_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_selfLieBasisVector
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_eR
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
theorem _root_.solution : ∀ k : Fin 4, ∃ k', φA U ιD e a χ k' = φB U ιG e a χ k := by
  intro k
  obtain ⟨_, _, _, h3, h4, h5⟩ :=
    eR (e := e) (ιD.onB.act (star a)) (ιD.onB.act a) (xc e χ (G := G)) (U.gt e).pG
  rw [eB U ιD ιG e a χ hO k]
  fin_cases k
  · exact ⟨Sum.inr 3, h3.trans (by rw [padd_comm]; rfl)⟩
  · exact ⟨Sum.inr 4, h4⟩
  · exact ⟨Sum.inr 5, h5⟩
  · exact ⟨Sum.inl 3, (selfLieBasisVector U e a χ).trans rfl⟩
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
