-- Prove2me | solution 1 for QECCertificates.hgp_Z_distance_ge_of_H1TKer_trivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:12.386802+00:00
-- url     : https://prove2.me/submissions/5f0d5489-ff54-4ec8-bd5a-0b38a5697dc1

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPTranspose
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaningDual
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_blockL_apply
public import Theorems.Thm_QECCertificates_blockR_apply
public import Theorems.Thm_QECCertificates_hammingNorm_swapBlocks
public import Theorems.Thm_QECCertificates_hgpHZ_mulVec_eq_zero_iff_swap
public import Theorems.Thm_QECCertificates_hgp_X_distance_ge_of_H1Ker_trivial
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_rowSpace_X_of_swap_mem_rowSpace_Z
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_readOff_nil
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.blockL_apply
attribute [local simp] QECCertificates.blockR_apply
attribute [local simp] QECCertificates.mem_kerL
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.readOff_nil
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHZ H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHX H₁ H₂).certificateRowSpace) {d₂ : ℕ}
    (hd₂ : ∀ w : Vec n₂, w ≠ 0 → H₂ *ᵥ w = 0 → d₂ ≤ hammingNorm w)
    (hT : ∀ u : Vec r₁, H₁.transpose *ᵥ u = 0 → u = 0) :
    d₂ ≤ hammingNorm v := by
  have hmain := hgp_X_distance_ge_of_H1Ker_trivial (H₁ := H₁.transpose)
    (H₂ := H₂.transpose) (v := fun c => v (swapBlocks c)) (d₂T := d₂)
    ((hgpHZ_mulVec_eq_zero_iff_swap H₁ H₂ v).mp hv)
    (fun hmem => hlog (mem_rowSpace_X_of_swap_mem_rowSpace_Z H₁ H₂ hmem))
    (fun w hw hw0 => hd₂ w hw (by simpa [Matrix.transpose_transpose] using hw0))
    hT
  rwa [hammingNorm_swapBlocks] at hmain
end QECCertificates
