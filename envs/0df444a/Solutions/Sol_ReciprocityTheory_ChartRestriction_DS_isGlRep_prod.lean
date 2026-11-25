-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.isGlRep_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:31:20.808254+00:00
-- url     : https://prove2.me/submissions/59c923d3-ef13-422b-8a19-67e989d68c20

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_prFst_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_prSnd_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_prod_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_prFst_prodE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_prSnd_prodE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.prFst_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.prSnd_apply

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
variable {E₁ : Fin n → Fin n → Module.End ℂ M₁} {E₂ : Fin n → Fin n → Module.End ℂ M₂}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE₁ : IsGlRep E₁) (hE₂ : IsGlRep E₂) : IsGlRep (prodE E₁ E₂) := by
  intro a b c d
  refine LinearMap.ext fun x => prod_ext ?_ ?_
  · have h := congrArg (fun X : Module.End ℂ M₁ => X (prFst x)) (hE₁ a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    change prFst _ = prFst _
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, prFst_prodE]
    rw [h]
    split_ifs <;> simp <;> rfl
  · have h := congrArg (fun X : Module.End ℂ M₂ => X (prSnd x)) (hE₂ a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    change prSnd _ = prSnd _
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, prSnd_prodE]
    rw [h]
    split_ifs <;> simp <;> rfl
end ReciprocityTheory.ChartRestriction.DS
