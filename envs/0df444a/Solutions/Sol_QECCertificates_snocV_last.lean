-- Prove2me | solution 1 for QECCertificates.snocV_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:44:06.868931+00:00
-- url     : https://prove2.me/submissions/07c33a3f-0b65-4695-99b3-6e58e4e5f259

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
public import Theorems.Thm_QECCertificates_snocV_castSucc
public import Theorems.Thm_QECCertificates_castSuccEmb_apply
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support


attribute [local simp] QECCertificates.snocV_castSucc
attribute [local simp] QECCertificates.castSuccEmb_apply

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {u : Vec n} {b : ZMod 2} : snocV u b (Fin.last n) = b := by
  simp only [snocV]
  rw [dif_neg (show ¬ ((Fin.last n : Fin (n + 1)) : ℕ) < n from by simp)]
end QECCertificates
