-- Prove2me | solution 1 for P2M_GroundTheory_GroupCoh_t__comp_t__09d0113656ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:40:27.774231+00:00
-- url     : https://prove2.me/submissions/6793050f-edda-4fc4-a0b1-0825b53986ea

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Theorems.Thm_GroundTheory_GroupCoh_tateCyclesMk_iCycles
import Theorems.Thm_GroundTheory_GroupCoh_tate_d_iCycles_int
import Theorems.Thm_P2M_GroundTheory_GroupCoh_t__apply_6f30be77357f
import Theorems.Thm_GroundTheory_GroupCoh_tateMap_comp_apply
import Theorems.Thm_GroundTheory_GroupCoh_tateMap_congr
import Theorems.Thm_GroundTheory_GroupCoh_tateMap_d_apply
import Theorems.Thm_GroundTheory_GroupCoh_tateMap_zero_apply
import Theorems.Thm_GroundTheory_GroupCoh_tateD_tateD_apply
import Theorems.Thm_GroundTheory_GroupCoh_tateMap_g_surjective
import Theorems.Thm_GroundTheory_GroupCoh_tateMap_f_injective
import Theorems.Thm_GroundTheory_GroupCoh_tateMap_exists_f_eq
import Theorems.Thm_GroundTheory_GroupCoh_tateCyclesMk_neg
import Theorems.Thm_GroundTheory_GroupCoh_cupCochainsTensor_tmul
import Theorems.Thm_P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.cupCochainsTensor_tmul
attribute [local simp] P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
variable (Q : ShortComplex (ShortComplex (Rep k G)))
  (hR₁ : Q.X₁.ShortExact) (hR₂ : Q.X₂.ShortExact) (hR₃ : Q.X₃.ShortExact)
  (hC₁ : (Q.map ShortComplex.π₁).ShortExact) (hC₂ : (Q.map ShortComplex.π₂).ShortExact)
  (hC₃ : (Q.map ShortComplex.π₃).ShortExact)
include hR₂ hC₂
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace GroundTheory.GroupCoh
theorem _root_.solution (p : ℤ) :
    tδ hC₃ p (p + 1) rfl ≫ tδ hR₁ (p + 1) (p + 1 + 1) rfl =
      -(tδ hR₃ p (p + 1) rfl ≫ tδ hC₁ (p + 1) (p + 1 + 1) rfl) := by
  apply (cancel_epi ((tateComplex Q.X₃.X₃).homologyπ p)).1
  ext z
  simp only [Preadditive.comp_neg, ModuleCat.hom_comp, ModuleCat.hom_neg, LinearMap.comp_apply,
    LinearMap.neg_apply]
  have hz := tate_d_iCycles_int _ _ z
  rw [← tateCyclesMk_iCycles _ _ z hz]
  set x33 := ((tateComplex Q.X₃.X₃).iCycles p).hom z
  have hQ : Q.f.τ₂ ≫ Q.g.τ₂ = 0 := by rw [← ShortComplex.comp_τ₂, Q.zero, ShortComplex.zero_τ₂]
  obtain ⟨x32, hx32⟩ := tateMap_g_surjective hR₃ p x33
  obtain ⟨x22, hx22⟩ : ∃ x22 : (tateComplex Q.X₂.X₂).X p,
      ((tateComplex.map Q.g.τ₂).f p).hom x22 = x32 := tateMap_g_surjective hC₂ p x32
  set x23 := ((tateComplex.map Q.X₂.g).f p).hom x22
  have hx23 : ((tateComplex.map Q.g.τ₃).f p).hom x23 = x33 := by
    rw [← tateMap_comp_apply, tateMap_congr Q.g.comm₂₃.symm, tateMap_comp_apply]
    exact (congrArg _ hx22).trans hx32
  have hb0 : ((tateComplex.map Q.g.τ₃).f (p + 1)).hom
      (((tateComplex Q.X₂.X₃).d p (p + 1)).hom x23) = 0 := by
    rw [tateMap_d_apply, hx23, hz]
  obtain ⟨b, hb⟩ : ∃ b : (tateComplex Q.X₁.X₃).X (p + 1), ((tateComplex.map Q.f.τ₃).f (p + 1)).hom b =
      ((tateComplex Q.X₂.X₃).d p (p + 1)).hom x23 := tateMap_exists_f_eq hC₃ (p + 1) _ hb0
  have hdb : ((tateComplex Q.X₁.X₃).d (p + 1) (p + 1 + 1)).hom b = 0 := by
    have h1 : ((tateComplex.map Q.f.τ₃).f (p + 1 + 1)).hom
        (((tateComplex Q.X₁.X₃).d (p + 1) (p + 1 + 1)).hom b) =
        ((tateComplex.map Q.f.τ₃).f (p + 1 + 1)).hom 0 := by
      rw [tateMap_d_apply, hb, tateD_tateD_apply, map_zero]
    exact tateMap_f_injective hC₃ (p + 1 + 1) h1
  have e1 := tδ_apply hC₃ p x33 hz x23 hx23 b hb hdb
  obtain ⟨c, hc⟩ := tateMap_g_surjective hR₁ (p + 1) b
  have hw0 : ((tateComplex.map Q.X₁.g).f (p + 1 + 1)).hom
      (((tateComplex Q.X₁.X₂).d (p + 1) (p + 1 + 1)).hom c) = 0 := by
    rw [tateMap_d_apply, hc, hdb]
  obtain ⟨w, hw⟩ := tateMap_exists_f_eq hR₁ (p + 1 + 1) _ hw0
  have hdw : ((tateComplex Q.X₁.X₁).d (p + 1 + 1) (p + 1 + 1 + 1)).hom w = 0 := by
    have h1 : ((tateComplex.map Q.X₁.f).f (p + 1 + 1 + 1)).hom
        (((tateComplex Q.X₁.X₁).d (p + 1 + 1) (p + 1 + 1 + 1)).hom w) =
        ((tateComplex.map Q.X₁.f).f (p + 1 + 1 + 1)).hom 0 := by
      rw [tateMap_d_apply, hw, tateD_tateD_apply, map_zero]
    exact tateMap_f_injective hR₁ _ h1
  have e2 := tδ_apply hR₁ (p + 1) b hdb c hc w hw hdw
  have he0 : ((tateComplex.map Q.X₂.g).f (p + 1)).hom
      (((tateComplex Q.X₂.X₂).d p (p + 1)).hom x22 - ((tateComplex.map Q.f.τ₂).f (p + 1)).hom c) = 0 := by
    rw [map_sub, tateMap_d_apply, ← tateMap_comp_apply Q.f.τ₂ Q.X₂.g, tateMap_congr Q.f.comm₂₃,
      tateMap_comp_apply, hc, sub_eq_zero]
    exact hb.symm
  obtain ⟨e, he⟩ := tateMap_exists_f_eq hR₂ (p + 1) _ he0
  have hge : ((tateComplex.map Q.X₃.f).f (p + 1)).hom (((tateComplex.map Q.g.τ₁).f (p + 1)).hom e) =
      ((tateComplex Q.X₃.X₂).d p (p + 1)).hom x32 := by
    rw [← tateMap_comp_apply, tateMap_congr Q.g.comm₁₂, tateMap_comp_apply, he, map_sub, tateMap_d_apply, hx22,
      ← tateMap_comp_apply Q.f.τ₂ Q.g.τ₂, tateMap_congr hQ, tateMap_zero_apply, sub_zero]
  have hdge : ((tateComplex Q.X₃.X₁).d (p + 1) (p + 1 + 1)).hom
      (((tateComplex.map Q.g.τ₁).f (p + 1)).hom e) = 0 := by
    have h1 : ((tateComplex.map Q.X₃.f).f (p + 1 + 1)).hom
        (((tateComplex Q.X₃.X₁).d (p + 1) (p + 1 + 1)).hom (((tateComplex.map Q.g.τ₁).f (p + 1)).hom e)) =
        ((tateComplex.map Q.X₃.f).f (p + 1 + 1)).hom 0 := by
      rw [tateMap_d_apply, hge, tateD_tateD_apply, map_zero]
    exact tateMap_f_injective hR₃ _ h1
  have e3 := tδ_apply hR₃ p x33 hz x32 hx32 _ hge hdge
  have hde : ((tateComplex.map Q.f.τ₁).f (p + 1 + 1)).hom (-w) =
      ((tateComplex Q.X₂.X₁).d (p + 1) (p + 1 + 1)).hom e := by
    apply tateMap_f_injective hR₂
    rw [map_neg, map_neg, ← tateMap_comp_apply, tateMap_congr Q.f.comm₁₂, tateMap_comp_apply, hw,
      tateMap_d_apply, tateMap_d_apply, he, map_sub, tateD_tateD_apply, zero_sub]
  have hdnw : ((tateComplex Q.X₁.X₁).d (p + 1 + 1) (p + 1 + 1 + 1)).hom (-w) = 0 := by
    rw [map_neg, hdw, neg_zero]
  have e4 := tδ_apply hC₁ (p + 1) _ hdge e rfl (-w) hde hdnw
  have e1' : (tδ hC₃ p (p + 1) rfl).hom (((tateComplex Q.X₃.X₃).homologyπ p).hom
      (tateCyclesMk Q.X₃.X₃ p x33 hz)) =
      ((tateComplex Q.X₁.X₃).homologyπ (p + 1)).hom (tateCyclesMk Q.X₁.X₃ (p + 1) b hdb) := e1
  have e4' : (tδ hC₁ (p + 1) (p + 1 + 1) rfl).hom (((tateComplex Q.X₃.X₁).homologyπ (p + 1)).hom
      (tateCyclesMk Q.X₃.X₁ (p + 1) (((tateComplex.map Q.g.τ₁).f (p + 1)).hom e) hdge)) =
      ((tateComplex Q.X₁.X₁).homologyπ (p + 1 + 1)).hom (tateCyclesMk Q.X₁.X₁ (p + 1 + 1) (-w) hdnw) := e4
  have key : (tδ hR₁ (p + 1) (p + 1 + 1) rfl).hom ((tδ hC₃ p (p + 1) rfl).hom
      (((tateComplex Q.X₃.X₃).homologyπ p).hom (tateCyclesMk Q.X₃.X₃ p x33 hz))) =
      -(tδ hC₁ (p + 1) (p + 1 + 1) rfl).hom ((tδ hR₃ p (p + 1) rfl).hom
        (((tateComplex Q.X₃.X₃).homologyπ p).hom (tateCyclesMk Q.X₃.X₃ p x33 hz))) := by
    rw [e1', e2, e3, e4', tateCyclesMk_neg _ _ w hdw hdnw, map_neg, neg_neg]
  exact key
end GroundTheory.GroupCoh
