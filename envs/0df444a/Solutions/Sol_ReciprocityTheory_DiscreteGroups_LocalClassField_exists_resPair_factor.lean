-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.exists_resPair_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:00:36.135799+00:00
-- url     : https://prove2.me/submissions/1b8d0e92-1325-40d6-8d93-507fae752435

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_equiv_subG
import Theorems.Thm_ReciprocityTheory_Coh_Cx_H_ind
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_Z_apply
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_comp_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_H
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_add
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_congr
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_d
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_neg
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_smul
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_sub
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_zero
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_Tmap_mk
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_dHom_apply
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_kerMap_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.H_cls
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.Z_apply
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.comp_f
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_H
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_f
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_add
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_d
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_eq_zero_iff
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_neg
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_smul
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_sub
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_zero
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.Tmap_mk
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.dHom_apply
attribute [local simp] ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.kerMap_coe



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K L}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (h : K ≤ L) :
    ∃ e : Pair ((kbarT p K).resSub (subG p K L)) (kbarT p L), (∀ n, Bijective (e.hom.H n)) ∧
      ∀ n x, (resPair h).hom.H n x =
        e.hom.H n ((Pair.res (kbarT p K) (subG p K L).subtype continuous_subtype_val).hom.H n x) := by
  obtain ⟨e, he, hc, hc'⟩ := exists_equiv_subG h
  let P : Pair ((kbarT p K).resSub (subG p K L)) (kbarT p L) :=
    { φ := e.toMonoidHom
      u := LinearMap.id
      φ_cont := hc
      u_cont := continuous_id
      equiv := fun g m => by
        show kbarRep p K (e g : GK p K) m = kbarRep p L g m
        rw [he]; rfl }
  let Q : Pair (kbarT p L) ((kbarT p K).resSub (subG p K L)) :=
    { φ := e.symm.toMonoidHom
      u := LinearMap.id
      φ_cont := hc'
      u_cont := continuous_id
      equiv := fun g m => by
        show kbarRep p L (e.symm g) m = kbarRep p K (g : GK p K) m
        have : (g : GK p K) = resGK h (e.symm g) := by rw [← he, e.apply_symm_apply]
        rw [this]; rfl }
  have hPQ : ∀ n x, P.hom.H n (Q.hom.H n x) = x := fun n x => by
    induction x using Cx.H_ind with
    | h x hx =>
      refine Cx.cls_congr _ _ (Subtype.ext (funext fun g => ?_))
      show x.1 (fun i => e.symm (e (g i))) = x.1 g
      simp
  have hQP : ∀ n x, Q.hom.H n (P.hom.H n x) = x := fun n x => by
    induction x using Cx.H_ind with
    | h x hx =>
      refine Cx.cls_congr _ _ (Subtype.ext (funext fun g => ?_))
      show x.1 (fun i => e (e.symm (g i))) = x.1 g
      simp
  refine ⟨P, fun n => ⟨LeftInverse.injective (hQP n), RightInverse.surjective (hPQ n)⟩, fun n x => ?_⟩
  induction x using Cx.H_ind with
  | h x hx =>
    refine Cx.cls_congr _ _ (Subtype.ext (funext fun g => ?_))
    show x.1 (fun i => resGK h (g i)) = x.1 (fun i => (e (g i) : GK p K))
    simp only [he]
end ReciprocityTheory.DiscreteGroups.LocalClassField
