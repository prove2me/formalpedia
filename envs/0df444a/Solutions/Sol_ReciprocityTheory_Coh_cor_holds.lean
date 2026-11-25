-- Prove2me | solution 1 for ReciprocityTheory.Coh.cor_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:39:29.049801+00:00
-- url     : https://prove2.me/submissions/480d40d2-e7cd-43bf-8c7f-57b07000ca24

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogIso
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Definitions.Def_ReciprocityTheory_GroupCohomology_InnerHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PartialProdCoe
import Definitions.Def_ReciprocityTheory_GroupCohomology_ResNormalHolds
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_comp_0576ef890fe4
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_congr_4a5e25450cfa
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_id_01b43f81e0f0
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_nsmul_8dc4b1f20659
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__card_rightRel_dc20959744a5
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__continuous_retr_0347f616e74e
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__inclCx_spec_0473f0a012a4
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__normCx_spec_5a505131bda6
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_mul_7e06b5c58710
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_out_180eaa669110
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
import Theorems.Thm_ReciprocityTheory_Coh_homogExists_holds
import Theorems.Thm_ReciprocityTheory_Coh_homogIso_holds
import Theorems.Thm_ReciprocityTheory_Coh_prism_holds
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
theorem _root_.solution : CorStatement.{u} := by
  intro R _ G _ _ _ M U _ hU
  obtain ⟨A, eA, hA⟩ := homogExists_holds R U (M.resSub U) G
  obtain ⟨eG, hG, hG1, hG2⟩ := homogIso_holds R G M
  obtain ⟨eU, hU0, hU1, hU2⟩ := homogIso_holds R U (M.resSub U)
  have P1 := prism_holds R U (M.resSub U) G U A (M.resSub U).coch eA eU hA hU0
  obtain ⟨φr, hφr⟩ := P1.1 (retr U) (continuous_retr U hU) (fun g x => retr_mul U g x)
  have P2 := prism_holds R U (M.resSub U) G G A A eA eA hA hA
  have ha : Continuous fun g : G => (retr U g : G) := continuous_subtype_val.comp (continuous_retr U hU)
  have hae : ∀ (g : U) (x : G), (retr U (g • x) : G) = g • (retr U x : G) := fun g x => by
    show (retr U ((g : G) * x) : G) = (g : G) * (retr U x : G)
    rw [retr_mul]; rfl
  obtain ⟨T, hT⟩ := P2.1 _ ha hae
  have hTid : ∀ n, T.H n = (Hom.id A).H n :=
    P2.2 _ id T (Hom.id A) ha continuous_id hae (fun _ _ => rfl) hT (fun _ _ _ => rfl)
  set N := normCx A eA hA eG hG
  set ι := inclCx A eA hA eG hG
  refine ⟨N.comp φr, ?_, ?_⟩
  · intro n f
    funext g
    rw [hG2 n _ g]
    show (eG n (N.f n (φr.f n f))).1 _ = _
    rw [normCx_spec]
    unfold normF corFun
    refine finsum_congr fun c => ?_
    congr 1
    rw [hφr, hU1]
    simp only [Fin.partialProd_zero, mul_one, retr_out, map_one, Module.End.one_apply]
    rfl
  · have hcomp : ∀ n f, (N.comp φr).f n ((Pair.res M U.subtype continuous_subtype_val).hom.f n f) =
        (N.comp (T.comp ι)).f n f := by
      intro n f
      apply (eG n).injective
      apply Subtype.ext
      show (eG n (N.f n _)).1 = (eG n (N.f n _)).1
      rw [normCx_spec, normCx_spec]
      funext x
      unfold normF
      refine finsum_congr fun c => ?_
      congr 1
      show (eA n (φr.f n _)).1 _ = (eA n (T.f n (ι.f n f))).1 _
      rw [hφr, hT, inclCx_spec, hU1, hG1]
      rfl
    have hNι : ∀ n f, (N.comp ι).f n f = U.index • f := by
      intro n f
      classical
      haveI : Fintype (Quotient (QuotientGroup.rightRel U)) := Fintype.ofFinite _
      apply (eG n).injective
      apply Subtype.ext
      rw [map_nsmul]
      show (eG n (N.f n (ι.f n f))).1 = _
      rw [normCx_spec]
      funext x
      refine (normF_eq M U n _ x).trans ?_
      have h1 : ∀ c : Quotient (QuotientGroup.rightRel U),
          M.rho c.out⁻¹ ((eA n (ι.f n f)).1 fun i => c.out * x i) = (eG n f).1 x := by
        intro c
        rw [inclCx_spec]
        have := (eG n f).2.2 c.out x
        simp only [smul_eq_mul] at this
        rw [this, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      simp only [h1, Finset.sum_const, Finset.card_univ, card_rightRel]
      rfl
    intro n x
    calc (N.comp φr).H n ((Pair.res M U.subtype continuous_subtype_val).hom.H n x)
        = ((N.comp φr).comp (Pair.res M U.subtype continuous_subtype_val).hom).H n x :=
          (Hom.H_comp _ _ n x).symm
      _ = (N.comp (T.comp ι)).H n x := by
          rw [Hom.H_congr _ _ (fun n f => hcomp n f)]
      _ = N.H n (T.H n (ι.H n x)) := by rw [Hom.H_comp, Hom.H_comp]
      _ = N.H n (ι.H n x) := by rw [hTid, Hom.H_id]
      _ = (N.comp ι).H n x := (Hom.H_comp _ _ n x).symm
      _ = U.index • x := Hom.H_nsmul _ _ n (hNι n) x
end ReciprocityTheory.Coh
