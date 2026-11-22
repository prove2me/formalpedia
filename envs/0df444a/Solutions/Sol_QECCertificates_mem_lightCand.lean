-- Prove2me | solution 1 for QECCertificates.mem_lightCand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:57:21.189023+00:00
-- url     : https://prove2.me/submissions/516c36a2-6f3f-43b0-ab57-ffe0004c91d8

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
public import Definitions.Def_LeanPool_QECCertificates_GF2_LowerBound
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_castSuccEmb_apply
public import Theorems.Thm_QECCertificates_lightVecs_nil
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
public import Theorems.Thm_QECCertificates_snocV_castSucc
public import Theorems.Thm_QECCertificates_snocV_last
public import Theorems.Thm_QECCertificates_snocV_zero_zero
public import Theorems.Thm_QECCertificates_wtRec_zero
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.castSuccEmb_apply
attribute [local simp] QECCertificates.lightVecs_nil
attribute [local simp] QECCertificates.mem_kerL
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil
attribute [local simp] QECCertificates.snocV_castSucc
attribute [local simp] QECCertificates.snocV_last
attribute [local simp] QECCertificates.snocV_zero_zero
attribute [local simp] QECCertificates.wtRec_zero



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {m₁ m₂ : ℕ}
    {M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)} {M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)}
    {d : ℕ} {v : Vec n} :
    v ∈ lightCand M₁ M₂ d ↔ v ∈ lightVecs n (d - 1) ∧ IsLightUndetectable M₁ M₂ v := by
  simp only [lightCand, List.mem_filter, decide_eq_true_eq, IsLightUndetectable, inSpanEch]
end QECCertificates
