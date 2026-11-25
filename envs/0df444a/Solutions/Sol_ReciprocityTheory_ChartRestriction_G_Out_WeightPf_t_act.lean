-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.WeightPf.t_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:17:59.828282+00:00
-- url     : https://prove2.me/submissions/69ea29d7-ecf4-4c31-bf2d-992d31c674a0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WchartPullLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_act_O__49ddb8c00205
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_cancel_sec_act
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_cancel_sec_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_rres
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LBVal_rres

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
namespace ReciprocityTheory.ChartRestriction.G.Out.WeightPf
open Semi
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
private lemma sres_val_lemma_2 {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    ((ReciprocityTheory.ChartRestriction.G.Semi.res h u : Γ(X, V)ˣ) : Γ(X, V)) =
      (X.presheaf.map (homOfLE h).op).hom (u : Γ(X, U)) := rfl
private lemma corr_val_lemma_3 {Y : Scheme.{0}} {OA OC OS A B C PS W : Y.Opens}
    {pA : A ≤ OA} {c1 : C ≤ OC} {m1 : B ≤ C} {pS : PS ≤ OS} {m2 : B ≤ PS}
    (xa : Γ(Y, OA)ˣ) (xc : Γ(Y, OC)ˣ) (xs : Γ(Y, OS)ˣ) (hW : W ≤ A ⊓ B)
    (h : ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_left : A ⊓ B ≤ A) (ReciprocityTheory.ChartRestriction.G.Semi.res pA xa) =
      ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_right : A ⊓ B ≤ B)
        (ReciprocityTheory.ChartRestriction.G.Semi.res m1 (ReciprocityTheory.ChartRestriction.G.Semi.res c1 xc) *
          ReciprocityTheory.ChartRestriction.G.Semi.res m2 (ReciprocityTheory.ChartRestriction.G.Semi.res pS xs))) :
    (Y.presheaf.map (homOfLE (hW.trans (inf_le_left.trans pA))).op).hom (xa : Γ(Y, OA)) =
      (Y.presheaf.map (homOfLE ((hW.trans inf_le_right).trans (m1.trans c1))).op).hom (xc : Γ(Y, OC)) *
      (Y.presheaf.map (homOfLE ((hW.trans inf_le_right).trans (m2.trans pS))).op).hom
        (xs : Γ(Y, OS)) := by
  have h2 := congrArg (fun u => ((ReciprocityTheory.ChartRestriction.G.Semi.res hW u : Γ(Y, W)ˣ) : Γ(Y, W))) h
  simp only [map_mul, Units.val_mul, sres_val_lemma_2, rres] at h2
  exact h2
end ReciprocityTheory.ChartRestriction.G.Out.WeightPf
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.WeightPf
open Semi
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
namespace ReciprocityTheory.ChartRestriction.G.Out.WeightPf
theorem _root_.solution (χ : D.X) (jt : Fin 4 → D.P.L.ι) (hjt : LB.Coh D.P.L (D.Oφ g.pG χ) jt)
    (W' : (Te D I e ⊗ thickObj R I e G).left.Opens)
    (hs : W' ≤ (snd (Te D I e) (thickObj R I e G)).left ⁻¹ᵁ LB.wchart D.P.L (D.Oφ g.pG χ) jt)
    (ha : W' ≤ (act g).left ⁻¹ᵁ LB.wchart D.P.L (D.Oφ g.pG χ) jt) :
    ((act g).left.appLE _ W' ha).hom ((g.t χ).s jt).val =
      ((Te D I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom
        (Semi.TorusInj.chiP D.X (thickObj R I e G) χ) *
      ((snd (Te D I e) (thickObj R I e G)).left.appLE _ W' hs).hom ((g.t χ).s jt).val := by
  have key := g.t_weight χ jt (Sum.elim PEmpty.elim jt)
    (fun k₁ k₂ h => hjt k₁ k₂ (cancel_sec_act g h))
    (by
      rintro (s₁ | k₁) (s₂ | k₂) h
      · exact s₁.elim
      · exact s₁.elim
      · exact s₂.elim
      · exact hjt k₁ k₂ (cancel_sec_snd h))
    (by
      rintro k (s | k') h
      · exact s.elim
      · exact hjt k k' (cancel_sec_snd ((act_Oφ g χ k).symm.trans h)))
  simp only [LB.pullGen, LB.mulGen, charGen] at key
  have hW1 : W' ≤ LB.wchart D.P.L (fun k => (lift (fst (Te D I e) (thickObj R I e G) ≫ g.i)
      (snd (Te D I e) (thickObj R I e G)) ≫ μ[thickObj R I e G]).left ≫ D.Oφ g.pG χ k) jt := by
    intro x hx
    have h1 : (act g).left.base x ∈ ⋂ k, (D.Oφ g.pG χ k).base ⁻¹' (D.P.L.U (jt k) : Set _) := ha hx
    exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 h1 k
  have hW2 : W' ≤ LB.wchart D.P.L
      (Sum.elim PEmpty.elim fun k => (snd (Te D I e) (thickObj R I e G)).left ≫ D.Oφ g.pG χ k)
      (Sum.elim PEmpty.elim jt) := by
    intro x hx
    have h1 : (snd (Te D I e) (thickObj R I e G)).left.base x ∈
        ⋂ k, (D.Oφ g.pG χ k).base ⁻¹' (D.P.L.U (jt k) : Set _) := hs hx
    refine Set.mem_iInter.2 ?_
    rintro (s | k)
    · exact s.elim
    · exact Set.mem_iInter.1 h1 k
  have hG := corr_val_lemma_3 _ _ _ (le_inf hW1 hW2) key
  exact hG
end ReciprocityTheory.ChartRestriction.G.Out.WeightPf
