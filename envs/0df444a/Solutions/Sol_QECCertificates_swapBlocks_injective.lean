-- Prove2me | solution 1 for QECCertificates.swapBlocks_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:36.159495+00:00
-- url     : https://prove2.me/submissions/8752b462-be8d-45da-860c-bf630f78e425

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPTranspose
public import Theorems.Thm_QECCertificates_swapBlocks_swapBlocks
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_blockL_apply
public import Theorems.Thm_QECCertificates_blockR_apply
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.blockL_apply
attribute [local simp] QECCertificates.blockR_apply
attribute [local simp] QECCertificates.mem_support



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution {α β : Type*} : Function.Injective (swapBlocks (α := α) (β := β)) := by
  intro a b hab
  have h := congrArg (swapBlocks (α := β) (β := α)) hab
  simpa only [swapBlocks_swapBlocks] using h
end QECCertificates
