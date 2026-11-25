-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.WeightPf.weightIndep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:48:19.866708+00:00
-- url     : https://prove2.me/submissions/abc485d7-f05a-4c9d-b402-07db144072e3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WeightIndep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_mem_finset_inf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_mem_of_finset_inf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_comp_base_eq
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_act_O__49ddb8c00205
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_act_left_pG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_rres
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_t_act
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LBVal_rres
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_appLE_of_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_eq_zero_of_sum


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.WeightPf
open Semi
set_option maxHeartbeats 1000000
namespace ReciprocityTheory.ChartRestriction.G.Out.WeightPf
theorem _root_.solution : WeightIndepSt := by
  intro R _ _ I D A G _ _ U e k σ f hσ hexp α j
  classical
  obtain ⟨S, hout, hmain⟩ := hexp
  by_cases hα : α ∉ S
  · exact hout α hα j
  push Not at hα
  refine TopCat.Presheaf.section_ext (thickObj R I e G).left.sheaf _ _ 0 fun x hx => ?_

  choose c0 hc0 using exists_chart D.toPre.P.L D.toPre.P.isLB
  let c : ((thickObj R I e G).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι := fun ψ => c0 (ψ.base x)
  have hc : ∀ ψ, ψ.base x ∈ D.toPre.P.L.U (c ψ) := fun ψ => hc0 _
  let p1 : PUnit → D.toPre.P.L.ι := fun _ => c (U.gt e).pG.left
  let jf : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun β k => c ((U.gt e).pG.left ≫ D.toPre.famφB β k)
  let jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun β k => c (D.toPre.Oφ (U.gt e).pG β k)
  let Vst : (thickObj R I e G).left.Opens :=
    LB.wchart D.toPre.P.L (fun _ : PUnit => (U.gt e).pG.left) p1 ⊓
      S.inf (fun β => (U.gt e).pG.left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β) ⊓
        LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG β) (jt β))
  have hVf : ∀ β ∈ S, Vst ≤ (U.gt e).pG.left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β) :=
    fun β hβ => inf_le_right.trans ((Finset.inf_le hβ).trans inf_le_left)
  have hVt : ∀ β ∈ S, Vst ≤ LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG β) (jt β) :=
    fun β hβ => inf_le_right.trans ((Finset.inf_le hβ).trans inf_le_right)
  have hxV : x ∈ Vst := by
    refine ⟨Set.mem_iInter.2 fun _ => hc _, mem_finset_inf _ _ _ fun β _ => ⟨?_, ?_⟩⟩
    · exact Set.mem_iInter.2 fun k => by
        have := hc ((U.gt e).pG.left ≫ D.toPre.famφB β k)
        rwa [Scheme.Hom.comp_apply] at this
    · exact Set.mem_iInter.2 fun k => hc _

  let Fv : ∀ β ∈ S, Γ((thickObj R I e G).left, Vst) := fun β hβ =>
    ((thickObj R I e G).left.presheaf.map (homOfLE (hVf β hβ)).op).hom
      (((U.gt e).pG.left.app _).hom ((f β).f (jf β)))
  let Tv : ∀ β ∈ S, Γ((thickObj R I e G).left, Vst) := fun β hβ =>
    (res (hVt β hβ) (((U.gt e).t β).s (jt β))).val
  let Φ : Γ((thickObj R I e G).left, Vst) := ∑ β ∈ S.attach, Fv β.1 β.2 * Tv β.1 β.2

  have hΦ : Φ = 0 := by
    refine TopCat.Presheaf.section_ext (thickObj R I e G).left.sheaf _ _ 0 fun y hy => ?_
    obtain ⟨i2, hi2⟩ := exists_chart U.LG.L U.LG.isLB ((fstG I e G).left.base y)
    let p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι) := (p1, fun _ => i2)
    let j₁ : Fin 1 → U.LG.L.ι := fun _ => i2
    have hcoh : CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2)))
        (Sum.elim (fun _ => p.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) := by
      intro a b hab
      have key : ∀ z, (Sum.elim (fun _ => p.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) z =
          c ((Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
            (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
              (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2))) z) := by
        rintro (z | z | z) <;> rfl
      rw [key a, key b, hab]
    have E := hmain p j₁ jf jt rfl hcoh
    have hyW : y ∈ U.expW e p j₁ S jf jt := by
      refine ⟨⟨⟨hy.1, Set.mem_iInter.2 fun _ => hi2⟩, Set.mem_iInter.2 fun _ => ?_⟩, hy.2⟩
      exact hi2
    have hWV : U.expW e p j₁ S jf jt ≤ Vst :=
      le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left)) inf_le_right
    have hres : ((thickObj R I e G).left.presheaf.map (homOfLE hWV).op).hom Φ =
        ∑ β ∈ S.attach,
          ((thickObj R I e G).left.presheaf.map (homOfLE (U.expW_le_f e p j₁ jf jt β.2)).op).hom
            (((U.gt e).pG.left.app _).hom ((f β.1).f (jf β.1))) *
          (res (U.expWeight_le_chart_weight e p j₁ jf jt β.2) (((U.gt e).t β.1).s (jt β.1))).val :=
      (map_sum _ _ _).trans (Finset.sum_congr rfl fun β _ => (map_mul _ _ _).trans
        (congrArg₂ (· * ·) (Semi.LBVal.rres _ _ _) (Semi.LBVal.rres _ _ _)))
    have hR := E.symm.trans (mul_eq_zero_of_right _ ((congrArg
      ((thickObj R I e G).left.presheaf.map (homOfLE (inf_le_left.trans inf_le_right :
        U.expW e p j₁ S jf jt ≤ (fstG I e G).left ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁)).op).hom
        (hσ j₁)).trans (map_zero _)))
    exact ((TopCat.Presheaf.germ_res_apply (thickObj R I e G).left.presheaf (homOfLE hWV) y hyW Φ).symm.trans
      ((congrArg _ (hres.trans hR)).trans (map_zero _))).trans (map_zero _).symm

  let g := U.gt e
  let W' : (Te D.toPre I e ⊗ thickObj R I e G).left.Opens := (snd (Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ Vst
  have hpt : ∀ (ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left),
      (act g).left ≫ ψ = (snd (Te D.toPre I e) (thickObj R I e G)).left ≫ ψ →
      ∀ z, ψ ((act g).left z) = ψ ((snd (Te D.toPre I e) (thickObj R I e G)).left z) :=
    fun ψ h z => comp_base_eq h z
  have hpG : (act g).left ≫ (U.gt e).pG.left = (snd (Te D.toPre I e) (thickObj R I e G)).left ≫ (U.gt e).pG.left :=
    act_left_pG g
  have ha : W' ≤ (act g).left ⁻¹ᵁ Vst := by
    intro z hz
    refine ⟨Set.mem_iInter.2 fun u => ?_, mem_finset_inf _ _ _ fun β hβ => ⟨Set.mem_iInter.2 fun k => ?_,
      Set.mem_iInter.2 fun k => ?_⟩⟩
    · simp only [Set.mem_preimage]
      rw [hpt _ hpG z]; exact Set.mem_iInter.1 hz.1 u
    · simp only [Set.mem_preimage]
      rw [hpt _ hpG z]
      exact Set.mem_iInter.1 (mem_of_finset_inf hz.2 hβ).1 k
    · simp only [Set.mem_preimage]
      rw [hpt _ (act_Oφ g β k) z]
      exact Set.mem_iInter.1 (mem_of_finset_inf hz.2 hβ).2 k

  have keyF : ∀ β (hβ : β ∈ S), ((act g).left.appLE Vst W' ha).hom (Fv β hβ) =
      ((snd (Te D.toPre I e) (thickObj R I e G)).left.app Vst).hom (Fv β hβ) := by
    intro β hβ
    have m : (U.gt e).pG.left.app (LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β)) ≫
        (thickObj R I e G).left.presheaf.map (homOfLE (hVf β hβ)).op ≫ (act g).left.appLE Vst W' ha =
        (U.gt e).pG.left.app (LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β)) ≫
        (thickObj R I e G).left.presheaf.map (homOfLE (hVf β hβ)).op ≫
        (snd (Te D.toPre I e) (thickObj R I e G)).left.app Vst := by
      rw [Scheme.Hom.app_eq_appLE (snd (Te D.toPre I e) (thickObj R I e G)).left, Scheme.Hom.map_appLE, Scheme.Hom.map_appLE,
        Scheme.Hom.app_eq_appLE (U.gt e).pG.left, Scheme.Hom.appLE_comp_appLE,
        Scheme.Hom.appLE_comp_appLE, Semi.TorusInj.appLE_of_eq hpG]
    exact congrArg (fun φ => φ.hom ((f β).f (jf β))) m
  have keyT : ∀ β (hβ : β ∈ S), ((act g).left.appLE Vst W' ha).hom (Tv β hβ) =
      ((Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom
        (Semi.TorusInj.chiP D.toPre.X (thickObj R I e G) β) *
      ((snd (Te D.toPre I e) (thickObj R I e G)).left.app Vst).hom (Tv β hβ) := by
    intro β hβ
    have hs : W' ≤ (snd (Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ
        LB.wchart D.toPre.P.L (D.toPre.Oφ g.pG β) (jt β) := fun z hz => hVt β hβ hz
    have ha' : W' ≤ (act g).left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.Oφ g.pG β) (jt β) :=
      fun z hz => hVt β hβ (ha hz)
    have T := t_act g β (jt β) (fun k1 k2 h => congrArg c h) W' hs ha'
    have m1 : (thickObj R I e G).left.presheaf.map (homOfLE (hVt β hβ)).op ≫ (act g).left.appLE Vst W' ha =
        (act g).left.appLE _ W' ha' := Scheme.Hom.map_appLE _ _ _
    have m2 : (thickObj R I e G).left.presheaf.map (homOfLE (hVt β hβ)).op ≫
        (snd (Te D.toPre I e) (thickObj R I e G)).left.app Vst =
        (snd (Te D.toPre I e) (thickObj R I e G)).left.appLE _ W' hs := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE]
    exact (congrArg (fun φ => φ.hom (((U.gt e).t β).s (jt β)).val) m1).trans
      (T.trans (congrArg (_ * ·) (congrArg (fun φ => φ.hom (((U.gt e).t β).s (jt β)).val) m2).symm))

  let chi : D.toPre.X → Γ((Te D.toPre I e ⊗ thickObj R I e G).left, W') := fun β =>
    ((Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom
      (Semi.TorusInj.chiP D.toPre.X (thickObj R I e G) β)
  let sn := ((snd (Te D.toPre I e) (thickObj R I e G)).left.app Vst).hom
  let hfun : D.toPre.X → Γ((thickObj R I e G).left, Vst) := fun β =>
    if hβ : β ∈ S then Fv β hβ * Tv β hβ else 0
  have hd : ∀ β (hβ : β ∈ S), hfun β = Fv β hβ * Tv β hβ := fun β hβ => by
    show (if hβ' : β ∈ S then Fv β hβ' * Tv β hβ' else 0) = _
    exact dif_pos hβ
  have hZ : ∑ β ∈ S.attach, chi β.1 * sn (Fv β.1 β.2 * Tv β.1 β.2) = 0 := by
    refine (Finset.sum_congr rfl fun β _ => ?_).trans
      ((map_sum ((act g).left.appLE Vst W' ha).hom _ _).symm.trans ((congrArg _ hΦ).trans (map_zero _)))
    exact ((congrArg (chi β.1 * ·) (map_mul sn _ _)).trans (mul_left_comm _ _ _)).trans
      ((map_mul ((act g).left.appLE Vst W' ha).hom _ _).trans
        (congrArg₂ (· * ·) (keyF β.1 β.2) (keyT β.1 β.2))).symm
  have hsum : ∑ β ∈ S, chi β * sn (hfun β) = 0 := by
    refine (Finset.sum_attach S (fun β => chi β * sn (hfun β))).symm.trans ((Finset.sum_congr rfl
      fun β _ => ?_).trans hZ)
    exact congrArg (fun z => chi β.1 * sn z) (hd β.1 β.2)
  have h0 := Semi.TorusInj.eq_zero_of_sum D.toPre.X (thickObj R I e G) S hfun hsum α hα
  have hFT : Fv α hα * Tv α hα = 0 := (hd α hα).symm.trans h0
  have hF : Fv α hα = 0 :=
    (Units.mul_left_eq_zero (res (hVt α hα) (((U.gt e).t α).s (jt α)))).mp hFT

  have hO1 : (U.gt e).pG.left ⁻¹ᵁ (LB.wchart D.toPre.P.L (D.toPre.famφB α) j ⊓
      LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α)) ≤
      (U.gt e).pG.left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB α) j := fun z hz => hz.1
  have hO2 : (U.gt e).pG.left ⁻¹ᵁ (LB.wchart D.toPre.P.L (D.toPre.famφB α) j ⊓
      LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α)) ≤
      (U.gt e).pG.left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α) := fun z hz => hz.2
  have hxO : x ∈ (U.gt e).pG.left ⁻¹ᵁ (LB.wchart D.toPre.P.L (D.toPre.famφB α) j ⊓
      LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α)) := ⟨hx, hVf α hα hxV⟩
  have nat1 : (U.gt e).pG.left.app (LB.wchart D.toPre.P.L (D.toPre.famφB α) j) ≫
      (thickObj R I e G).left.presheaf.map (homOfLE hO1).op =
      D.toPre.P.A.left.presheaf.map (homOfLE (inf_le_left : LB.wchart D.toPre.P.L (D.toPre.famφB α) j ⊓
        LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α) ≤ _)).op ≫
      (U.gt e).pG.left.app _ := ((U.gt e).pG.left.naturality _).symm
  have nat2 : (U.gt e).pG.left.app (LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α)) ≫
      (thickObj R I e G).left.presheaf.map (homOfLE hO2).op =
      D.toPre.P.A.left.presheaf.map (homOfLE (inf_le_right : LB.wchart D.toPre.P.L (D.toPre.famφB α) j ⊓
        LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α) ≤ _)).op ≫
      (U.gt e).pG.left.app _ := ((U.gt e).pG.left.naturality _).symm
  have hsecond : ((thickObj R I e G).left.presheaf.germ _ x hxO).hom
      (((U.gt e).pG.left.app _).hom ((D.toPre.P.A.left.presheaf.map (homOfLE (inf_le_right :
        LB.wchart D.toPre.P.L (D.toPre.famφB α) j ⊓ LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α) ≤ _)).op).hom
          ((f α).f (jf α)))) = 0 :=
    (congrArg ((thickObj R I e G).left.presheaf.germ _ x hxO).hom
      (congrArg (fun φ => φ.hom ((f α).f (jf α))) nat2).symm).trans
      ((TopCat.Presheaf.germ_res_apply _ (homOfLE hO2) x hxO _).trans
        ((TopCat.Presheaf.germ_res_apply _ (homOfLE (hVf α hα)) x hxV _).symm.trans
          ((congrArg _ hF).trans (map_zero _))))
  exact ((TopCat.Presheaf.germ_res_apply _ (homOfLE hO1) x hxO _).symm.trans
    ((congrArg _ ((congrArg (fun φ => φ.hom ((f α).f j)) nat1).trans
      ((congrArg ((U.gt e).pG.left.app (LB.wchart D.toPre.P.L (D.toPre.famφB α) j ⊓
        LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α))).hom ((f α).compat j (jf α))).trans
          (map_mul _ _ _)))).trans
      ((map_mul _ _ _).trans ((congrArg _ hsecond).trans (mul_zero _))))).trans (map_zero _).symm
end ReciprocityTheory.ChartRestriction.G.Out.WeightPf
