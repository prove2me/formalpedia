-- Prove2me | solution 1 for QECCertificates.rank_hgpHZ_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:47.152798+00:00
-- url     : https://prove2.me/submissions/2684f730-a7a6-4201-ae06-17eae497a7e7

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPTranspose
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPKunneth
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_blockL_apply
public import Theorems.Thm_QECCertificates_blockR_apply
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_mulVec_swap_eq
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
public import Theorems.Thm_QECCertificates_swapBlocks_swapBlocks
public import Theorems.Thm_QECCertificates_vee_apply
public import Theorems.Thm_QECCertificates_wedge_apply
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.blockL_apply
attribute [local simp] QECCertificates.blockR_apply
attribute [local simp] QECCertificates.mem_kerL
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil
attribute [local simp] QECCertificates.vee_apply
attribute [local simp] QECCertificates.wedge_apply



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {p q r s : ℕ} {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution (A : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (B : Matrix (Fin r₂) (Fin n₂) (ZMod 2)) :
    (hgpHZ A B).rank = (hgpHX A.transpose B.transpose).rank := by
  have hrange : LinearMap.range (hgpHZ A B).mulVecLin
      = LinearMap.range (hgpHX A.transpose B.transpose).mulVecLin := by
    ext X
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨fun c => v (swapBlocks c), by
        funext x
        rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, mulVec_swap_eq]⟩
    · rintro ⟨w, rfl⟩
      exact ⟨fun c => w (swapBlocks c), by
        funext x
        rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, mulVec_swap_eq]
        congr 1
        funext c
        simp only [swapBlocks_swapBlocks]⟩
  rw [Matrix.rank, Matrix.rank, hrange]
end QECCertificates
