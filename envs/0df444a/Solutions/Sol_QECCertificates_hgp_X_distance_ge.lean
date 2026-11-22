-- Prove2me | solution 1 for QECCertificates.hgp_X_distance_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:17.500845+00:00
-- url     : https://prove2.me/submissions/b3a5648a-d9e6-4508-a01f-dafa3572a541

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Theorems.Thm_QECCertificates_mulVec_mem_spanL_colList
public import Theorems.Thm_QECCertificates_exists_mul_eq_of_rows_mem
public import Theorems.Thm_QECCertificates_blockL_rows_mem_of_small
public import Theorems.Thm_QECCertificates_blockR_cols_mem_of_small
public import Theorems.Thm_QECCertificates_exists_cleaning_cert
public import Theorems.Thm_QECCertificates_mem_rowSpace_hgpHZ_of_blocks
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_blockL_apply
public import Theorems.Thm_QECCertificates_blockR_apply
public import Theorems.Thm_QECCertificates_hgpHX_mulVec_eq_zero_iff
public import Theorems.Thm_QECCertificates_mem_kerL
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
    (hv : hgpHX H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ H₁ H₂).certificateRowSpace) {d₁ d₂T : ℕ}
    (hd₁ : ∀ w : Vec n₁, w ≠ 0 → H₁ *ᵥ w = 0 → d₁ ≤ hammingNorm w)
    (hd₂ : ∀ w : Vec r₂, w ≠ 0 → H₂.transpose *ᵥ w = 0 → d₂T ≤ hammingNorm w) :
    min d₁ d₂T ≤ hammingNorm v := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  have hcomp : H₁ * blockL v = blockR v * H₂ := (hgpHX_mulVec_eq_zero_iff H₁ H₂ v).mp hv
  have hsmall₁ : hammingNorm v < d₁ := lt_of_lt_of_le hlt (min_le_left _ _)
  have hsmall₂ : hammingNorm v < d₂T := lt_of_lt_of_le hlt (min_le_right _ _)
  obtain ⟨C₀, hC₀⟩ := exists_mul_eq_of_rows_mem H₂ (blockL v)
    (fun a => blockL_rows_mem_of_small hcomp hd₁ hsmall₁ a)
  have hcol : ∀ j, (fun i => (blockR v + H₁ * C₀) i j) ∈ spanL (colList H₁) := by
    intro j
    change ((fun i => blockR v i j) + fun i => (H₁ * C₀) i j) ∈ spanL (colList H₁)
    refine Submodule.add_mem _ ?_ ?_
    · exact blockR_cols_mem_of_small (H₁ := H₁) (H₂ := H₂) hcomp hd₂ hsmall₂ j
    · change H₁ *ᵥ (fun t => C₀ t j) ∈ spanL (colList H₁)
      exact mulVec_mem_spanL_colList H₁ (fun t => C₀ t j)
  have hrowρ : (blockR v + H₁ * C₀) * H₂ = 0 := by
    rw [Matrix.add_mul]
    have h2 : H₁ * C₀ * H₂ = blockR v * H₂ := by
      have hassoc : H₁ * C₀ * H₂ = H₁ * (C₀ * H₂) := by simp only [Matrix.mul_assoc]
      rw [hassoc, hC₀, hcomp]
    rw [h2]
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  obtain ⟨D, hD₁, hD₂⟩ := exists_cleaning_cert (H₁ := H₁) (H₂ := H₂) hcol hrowρ
  refine hlog ?_
  refine mem_rowSpace_hgpHZ_of_blocks (C := C₀ + D) ?_ ?_
  · rw [Matrix.add_mul, hC₀, hD₂, add_zero]
  · rw [Matrix.mul_add, hD₁]
    have key : ∀ a b : ZMod 2, a + (b + a) = b := by
      intro a b
      rw [add_comm b a, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    ext i j
    simp only [Matrix.add_apply]
    exact (key _ _).symm
end QECCertificates
