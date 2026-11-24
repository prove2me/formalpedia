-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.kp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:44:34.800412+00:00
-- url     : https://prove2.me/submissions/dc2bae70-34c7-4083-89f6-949217d8b03e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp

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
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf
theorem _root_.solution (ρ : Γ((thickObj R I e G).left, ⊤))
    (h : (WeightPf.act g).left.appTop.hom ρ =
      (snd (WeightPf.Te D I e) (thickObj R I e G)).left.appTop.hom ρ)
    {Z : Scheme.{0}} (y1 y2 : Z ⟶ (thickObj R I e G).left) (hq : y1 ≫ g.q.left = y2 ≫ g.q.left) :
    y1.appTop.hom ρ = y2.appTop.hom ρ := by
  have hw : y1 ≫ (thickObj R I e G).hom = y2 ≫ (thickObj R I e G).hom := by
    rw [← Over.w g.q, ← Category.assoc, hq, Category.assoc]
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (y2 ≫ (thickObj R I e G).hom)
  let z1 : FinalForm ⟶ thickObj R I e G := Over.homMk y1 hw
  let z2 : FinalForm ⟶ thickObj R I e G := Over.homMk y2 rfl
  have hq' : z1 ≫ g.q = z2 ≫ g.q := Over.OverMorphism.ext (by simpa [z1, z2] using hq)
  have := g.q_hom
  have hinv : z2⁻¹ ≫ g.q = (z2 ≫ g.q)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← MonObj.mul_comp, inv_mul_cancel, MonObj.one_comp]
  have hd : (z1 * z2⁻¹) ≫ g.q = toUnit FinalForm ≫ η[thickObj R I e D.P.A] := by
    rw [MonObj.mul_comp, hinv, hq', mul_inv_cancel, Hom.one_def]
  let τ := g.isKernel.lift (z1 * z2⁻¹) (toUnit FinalForm) hd
  have hτ : τ ≫ g.i = z1 * z2⁻¹ := g.isKernel.lift_fst _ _ _
  have e1 : lift τ z2 ≫ WeightPf.act g = z1 := by
    have h1 : WeightPf.act g = (fst (WeightPf.Te D I e) (thickObj R I e G) ≫ g.i) * snd _ _ := rfl
    rw [h1, MonObj.comp_mul, lift_fst_assoc, lift_snd, hτ, inv_mul_cancel_right]
  have e2 : lift τ z2 ≫ snd (WeightPf.Te D I e) (thickObj R I e G) = z2 := lift_snd _ _
  have E1 : y1 = (lift τ z2).left ≫ (WeightPf.act g).left := by
    rw [← Over.comp_left, e1]; rfl
  have E2 : y2 = (lift τ z2).left ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left := by
    rw [← Over.comp_left, e2]; rfl
  rw [E1, E2, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    CommRingCat.comp_apply, h]
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
