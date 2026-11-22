-- Prove2me | solution 1 for QECCertificates.hgp_X_distance_ge_of_rowClean_free
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:16.993144+00:00
-- url     : https://prove2.me/submissions/6a70e9b6-27d7-4cc5-8df5-7124bcf89640

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Theorems.Thm_QECCertificates_mulVec_mem_spanL_colList
public import Theorems.Thm_QECCertificates_exists_mul_eq_of_rows_mem
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
theorem _root_.solution
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ H₁ H₂).certificateRowSpace) {d₂T : ℕ}
    (hd₂ : ∀ w : Vec r₂, w ≠ 0 → H₂.transpose *ᵥ w = 0 → d₂T ≤ hammingNorm w)
    (hrow : ∀ a, (fun b => blockL v a b) ∈ spanL (matRowList H₂)) :
    d₂T ≤ hammingNorm v := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  have hcomp : H₁ * blockL v = blockR v * H₂ := (hgpHX_mulVec_eq_zero_iff H₁ H₂ v).mp hv
  obtain ⟨C, hC⟩ := exists_mul_eq_of_rows_mem H₂ (blockL v) hrow
  have hrowρ : (blockR v + H₁ * C) * H₂ = 0 := by
    rw [Matrix.add_mul]
    have h2 : H₁ * C * H₂ = blockR v * H₂ := by
      have hassoc : H₁ * C * H₂ = H₁ * (C * H₂) := by simp only [Matrix.mul_assoc]
      rw [hassoc, hC, hcomp]
    rw [h2]
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hcolρ : ∀ j, (fun i => (blockR v + H₁ * C) i j) ∈ spanL (colList H₁) := by
    intro j
    change ((fun i => blockR v i j) + fun i => (H₁ * C) i j) ∈ spanL (colList H₁)
    refine Submodule.add_mem _ ?_ ?_
    · exact blockR_cols_mem_of_small hcomp hd₂ hlt j
    · change H₁ *ᵥ (fun t => C t j) ∈ spanL (colList H₁)
      exact mulVec_mem_spanL_colList H₁ (fun t => C t j)
  obtain ⟨D, hD₁, hD₂⟩ := exists_cleaning_cert (H₁ := H₁) (H₂ := H₂) hcolρ hrowρ
  refine hlog ?_
  refine mem_rowSpace_hgpHZ_of_blocks (C := C + D) ?_ ?_
  · rw [Matrix.add_mul, hC, hD₂, add_zero]
  · rw [Matrix.mul_add, hD₁]
    have key : ∀ a b : ZMod 2, a + (b + a) = b := by
      intro a b
      rw [add_comm b a, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    ext i j
    simp only [Matrix.add_apply]
    exact (key _ _).symm
end QECCertificates
