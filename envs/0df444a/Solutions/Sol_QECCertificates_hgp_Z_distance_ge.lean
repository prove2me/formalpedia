-- Prove2me | solution 1 for QECCertificates.hgp_Z_distance_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:57.872428+00:00
-- url     : https://prove2.me/submissions/c25709f7-1ed7-4a02-a454-081bbe8aaca2

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
public import Theorems.Thm_QECCertificates_hgp_X_distance_ge
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
theorem _root_.solution (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHZ H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHX H₁ H₂).certificateRowSpace) {d₁T d₂ : ℕ}
    (hd₁ : ∀ w : Vec r₁, w ≠ 0 → H₁.transpose *ᵥ w = 0 → d₁T ≤ hammingNorm w)
    (hd₂ : ∀ w : Vec n₂, w ≠ 0 → H₂ *ᵥ w = 0 → d₂ ≤ hammingNorm w) :
    min d₁T d₂ ≤ hammingNorm v := by
  have hmain := hgp_X_distance_ge (H₁ := H₁.transpose) (H₂ := H₂.transpose)
    (v := fun c => v (swapBlocks c)) (d₁ := d₁T) (d₂T := d₂)
    ((hgpHZ_mulVec_eq_zero_iff_swap H₁ H₂ v).mp hv)
    (fun hmem => hlog (mem_rowSpace_X_of_swap_mem_rowSpace_Z H₁ H₂ hmem))
    hd₁
    (fun w hw hw0 => hd₂ w hw (by simpa [Matrix.transpose_transpose] using hw0))
  rwa [hammingNorm_swapBlocks] at hmain
end QECCertificates
