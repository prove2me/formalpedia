-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.sameSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:25:52.318921+00:00
-- url     : https://prove2.me/submissions/195de28a-e961-48d9-ae66-0a562b2ffa73

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_CanonGenIsGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_OrbitMapConjSmulZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_padd_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ite_neg_one_eq_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_hA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_hBv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf
open Semi
section Fam
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
end Fam
section Eqs
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
end Eqs
section Sums
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))
private lemma ss_lemma {Y X : Scheme.{0}} (pB x Pa u0 pA xs P : Y ⟶ X) :
    LB.SameSum ![pB, x, Pa, u0] Oinvε (Sum.elim ![pA, xs, P, u0] ![pA, xs, P, pB, x, Pa])
      (Sum.elim Oinvε rosatiε) := by
  intro ψ
  simp only [Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_six]
  show @ite ℤ (pB = ψ) (Classical.propDecidable _) (-1) 0 +
      @ite ℤ (x = ψ) (Classical.propDecidable _) (1) 0 +
      @ite ℤ (Pa = ψ) (Classical.propDecidable _) (1) 0 +
      @ite ℤ (u0 = ψ) (Classical.propDecidable _) (-1) 0 =
    (@ite ℤ (pA = ψ) (Classical.propDecidable _) (-1) 0 +
      @ite ℤ (xs = ψ) (Classical.propDecidable _) (1) 0 +
      @ite ℤ (P = ψ) (Classical.propDecidable _) (1) 0 +
      @ite ℤ (u0 = ψ) (Classical.propDecidable _) (-1) 0) +
    (@ite ℤ (pA = ψ) (Classical.propDecidable _) (1) 0 +
      @ite ℤ (xs = ψ) (Classical.propDecidable _) (-1) 0 +
      @ite ℤ (P = ψ) (Classical.propDecidable _) (-1) 0 +
      @ite ℤ (pB = ψ) (Classical.propDecidable _) (-1) 0 +
      @ite ℤ (x = ψ) (Classical.propDecidable _) (1) 0 +
      @ite ℤ (Pa = ψ) (Classical.propDecidable _) (1) 0)
  simp only [ite_neg_one_eq_neg]
  ring
end Sums
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
end
end

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
theorem _root_.solution : LB.SameSum (φB U ιG e a χ) Oinvε (φA U ιD e a χ) εA := by
  rw [hA U ιD e a χ, hBv U ιD ιG e a χ hO,
    padd_comm D.toPre.P.A (xc e χ (G := G) ≫ ιD.onB.act (star a)) (U.gt e).pG,
    padd_comm D.toPre.P.A (xc e χ (G := G)) ((U.gt e).pG ≫ ιD.onB.act a)]
  exact ss_lemma _ _ _ _ _ _ _
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
