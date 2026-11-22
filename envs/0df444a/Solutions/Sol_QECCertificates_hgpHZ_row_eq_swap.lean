-- Prove2me | solution 1 for QECCertificates.hgpHZ_row_eq_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:20.537877+00:00
-- url     : https://prove2.me/submissions/1a79c935-0ef7-4806-8715-824d4e54d516

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPTranspose
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_blockL_apply
public import Theorems.Thm_QECCertificates_blockR_apply
public import Theorems.Thm_QECCertificates_hgpHZ_transpose_inputs_apply
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
theorem _root_.solution (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) (x : Fin n₁ × Fin r₂) :
    hgpHZ H₁ H₂ x = fun c => hgpHX H₁.transpose H₂.transpose x (swapBlocks c) := by
  funext c
  rcases c with ab | st
  · have h := hgpHZ_transpose_inputs_apply H₁.transpose H₂.transpose x (Sum.inl ab)
    simpa only [Equiv.sumComm_apply, swapBlocks, Matrix.transpose_transpose] using h
  · have h := hgpHZ_transpose_inputs_apply H₁.transpose H₂.transpose x (Sum.inr st)
    simpa only [Equiv.sumComm_apply, swapBlocks, Matrix.transpose_transpose] using h
end QECCertificates
