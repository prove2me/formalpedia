-- Prove2me | solution 1 for ReciprocityTheory.Coh.resNormal_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:29:04.959453+00:00
-- url     : https://prove2.me/submissions/8ba2def9-4bda-49a9-9658-bb863be7fd23

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogIso
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Definitions.Def_ReciprocityTheory_GroupCohomology_InnerHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PartialProdCoe
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
import Theorems.Thm_ReciprocityTheory_Coh_cor_holds
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_comp_0576ef890fe4
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_sum_2c8caae4364b
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__card_rightRel_dc20959744a5
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__partialProd_coe_64de18ea0922
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__rep_out_4a7c7e650af4
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_conj_4a4d3489c1a5
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_Z_apply
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_comp_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_H
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_add
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_d
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_neg
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_smul
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_sub
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_zero
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



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function CohomologyFunctoriality₂
universe u
namespace ReciprocityTheory.Coh
theorem _root_.solution : ResNormalStatement.{u} := by
  intro R _ G _ _ _ M N _ _ hN hunit n x hx
  classical
  haveI : Fintype (Quotient (QuotientGroup.rightRel N)) := Fintype.ofFinite _
  obtain ⟨cor, hcor, -⟩ := cor_holds R G M N hN
  set res := (Pair.res M N.subtype continuous_subtype_val).hom
  have key : ∀ f, (res.comp cor).f n f = ∑ c : Quotient (QuotientGroup.rightRel N),
      (conjPrime₂ M N c.out⁻¹).hom.f n f := by
    intro f
    apply Subtype.ext
    funext g
    show (cor.f n f).1 (fun i => (g i : G)) = _
    rw [hcor]
    erw [Submodule.coe_sum]
    rw [Finset.sum_apply]
    unfold corFun
    rw [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun c _ => ?_
    show _ = M.rho c.out⁻¹ (f.1 fun i => conjHom N c.out⁻¹ (g i))
    refine congrArg (M.rho c.out⁻¹) (congrArg f.1 (funext fun i => ?_))
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [retr_conj N _ _ (by rw [partialProd_coe]; exact SetLike.coe_mem _),
      retr_conj N _ _ (by rw [partialProd_coe]; exact SetLike.coe_mem _), rep_out,
      Fin.partialProd_succ]
    show _ = (c.out⁻¹)⁻¹ * (g i : G) * c.out⁻¹
    group
  have hrc : res.H n (cor.H n x) = N.index • x := by
    rw [← Hom.H_comp, Hom.H_sum _ _ _ n key]
    rw [Finset.sum_congr rfl fun c _ => hx c.out⁻¹ (conjPrime₂ M N c.out⁻¹) (fun _ => rfl) (fun _ => rfl)]
    rw [Finset.sum_const, Finset.card_univ, card_rightRel]
  refine ⟨cor.H n (((hunit.unit⁻¹ : Rˣ) : R) • x), ?_⟩
  rw [map_smul, map_smul, hrc, ← Nat.cast_smul_eq_nsmul R, smul_smul, hunit.val_inv_mul, one_smul]
end ReciprocityTheory.Coh
