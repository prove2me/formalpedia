-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity.corr_one_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:39.917125+00:00
-- url     : https://prove2.me/submissions/d1428fb0-9dec-4554-b3bb-ef1e78d99b2e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_PairProp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ResEqOfResEq
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_map_rfl__124873d90145
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_res_eq_of_res_eq__709669c04f21
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
namespace ZeroLinearity
section SlopeTestRemainingChoices
variable {X Y Z W : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
private lemma res_one_lemma {U V : Y.Opens} (h : V ≤ U) : res h (1 : Γ(Y, U)ˣ) = 1 :=
  Units.ext (map_one _)
end SlopeTestRemainingChoices
section Z
variable {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (f g : B ⟶ B) [IsMonHom g]
end Z
section Unit
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιG : RingAct G O) (e : ℕ) (a : O)
end Unit
end ZeroLinearity
open ZeroLinearity
section Main
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))
  (u : LB.Gen (LB.LinComb D.toPre.P.L
    (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε))
end Main
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
open ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
variable {X Y Z W : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
theorem _root_.solution {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    (h : LB.Gen.Corr L φ ε PEmpty.elim PEmpty.elim t (LB.oneGen L)) (j : K → L.ι)
    (hj : LB.Coh L φ j) : t.s j = 1 := by
  have hC : LB.Coh L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun k => k.elim
  have h2 : (L.LinComb φ ε).U j ≤
      (L.LinComb (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim).U PEmpty.elim := by
    delta LB.LinComb
    simp [LB.wchart]
  have key := res_eq_of_res_eq' _ _ le_rfl h2 (h j PEmpty.elim hj hC fun _ k' _ => k'.elim)
  change res _ (t.s j) = res _ 1 at key
  rw [res_one_lemma] at key
  have e : res (le_refl _) (t.s j) = t.s j := Units.ext (map_rfl' _)
  rw [← e]
  exact key
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
