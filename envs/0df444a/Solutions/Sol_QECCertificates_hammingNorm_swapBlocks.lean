-- Prove2me | solution 1 for QECCertificates.hammingNorm_swapBlocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:55:26.462797+00:00
-- url     : https://prove2.me/submissions/3d2cb156-8134-478d-b626-0cacda09fc7b

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPTranspose
public import Theorems.Thm_QECCertificates_swapBlocks_swapBlocks
public import Theorems.Thm_QECCertificates_swapBlocks_injective
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_blockL_apply
public import Theorems.Thm_QECCertificates_blockR_apply
public import Theorems.Thm_QECCertificates_hammingNorm_le_of_injective
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
theorem _root_.solution
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    hammingNorm (fun c => v (swapBlocks c)) = hammingNorm v := by
  have h₁ : hammingNorm (fun c : (Fin r₁ × Fin r₂) ⊕ (Fin n₁ × Fin n₂) => v (swapBlocks c))
      ≤ hammingNorm v :=
    hammingNorm_le_of_injective (fun c => swapBlocks c)
      (fun _ _ hab => swapBlocks_injective hab) v
  have h₂ : hammingNorm v
      ≤ hammingNorm (fun c : (Fin r₁ × Fin r₂) ⊕ (Fin n₁ × Fin n₂) => v (swapBlocks c)) := by
    have h := hammingNorm_le_of_injective (swapBlocks (α := (Fin n₁ × Fin n₂)) (β := (Fin r₁ × Fin
      r₂)))
      (swapBlocks_injective) (fun c => v (swapBlocks c))
    simpa only [swapBlocks_swapBlocks] using h
  exact le_antisymm h₁ h₂
end QECCertificates
