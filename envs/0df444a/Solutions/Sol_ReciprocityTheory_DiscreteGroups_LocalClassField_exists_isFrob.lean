-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.exists_isFrob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:12:32.161813+00:00
-- url     : https://prove2.me/submissions/979f8efc-2cda-480f-8347-1498adb7fdef

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_dvd_qK_pow_sub_one
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isFrob_iff
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
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_Tmap_mk
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_dHom_apply
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_kerMap_coe
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_IsFrobOn_of_dvd
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_isFrobOn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isFrobOn_iff
import Theorems.Thm_ReciprocityTheory_Gal_isClosed_setOf_apply
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
variable {p K}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) : ∃ σ : GK p K, IsFrob p K σ := by
  let S : ℕ → Set (GK p K) := fun k => {σ | IsFrobOn p K (k + 1).factorial σ}
  have hS : ∀ k, S k = ⋂ ζ : PadicAlgCl p, ⋂ _ : ζ ^ (qK p K ^ (k + 1).factorial - 1) = 1,
      {σ : GK p K | σ ζ = ζ ^ qK p K} := by
    intro k
    ext σ
    simp only [S, Set.mem_ofPred_eq, Set.mem_iInter]
    exact isFrobOn_iff p K hK (Nat.factorial_pos _) σ
  have hcl : ∀ k, IsClosed (S k) := by
    intro k
    rw [hS]
    exact isClosed_iInter fun ζ => isClosed_iInter fun _ =>
      ReciprocityTheory.Gal.isClosed_setOf_apply ζ (fun y => y = ζ ^ qK p K)
  have hne : ∀ k, (S k).Nonempty := fun k => exists_isFrobOn p K hK (Nat.factorial_pos _)
  have hmono : ∀ k, S (k + 1) ⊆ S k := fun k σ hσ =>
    IsFrobOn.of_dvd p K hK (Nat.factorial_dvd_factorial (Nat.le_succ _)) hσ
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hmono hne
    (hcl 0).isCompact hcl
  refine ⟨σ, (isFrob_iff hK σ).2 fun ζ m hm hζ => ?_⟩
  obtain ⟨n, hn, d, hd⟩ := exists_dvd_qK_pow_sub_one hK hm
  have h1 : IsFrobOn p K n σ := by
    have h2 : IsFrobOn p K ((n - 1) + 1).factorial σ := Set.mem_iInter.1 hσ (n - 1)
    refine IsFrobOn.of_dvd p K hK ?_ h2
    rw [Nat.sub_add_cancel hn]
    exact Nat.dvd_factorial hn le_rfl
  exact (isFrobOn_iff p K hK hn σ).1 h1 ζ (by rw [hd, pow_mul, hζ, one_pow])
end ReciprocityTheory.DiscreteGroups.LocalClassField
