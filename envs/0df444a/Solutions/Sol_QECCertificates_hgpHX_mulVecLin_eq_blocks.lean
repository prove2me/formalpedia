-- Prove2me | solution 1 for QECCertificates.hgpHX_mulVecLin_eq_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:23.068132+00:00
-- url     : https://prove2.me/submissions/3c3bbce3-c8d4-41fb-a623-7ae0ae0e490a

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPTranspose
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPKunneth
public import Theorems.Thm_QECCertificates_hgpHX_mulVec_apply


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {p q r s : ℕ} {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution (A : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (B : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    (hgpHX A B).mulVecLin v
      = mulLeft (s := n₂) A (blkL v) + mulRight (p := r₁) B (blkR v) := by
  funext ij
  obtain ⟨i, j⟩ := ij
  rw [Matrix.mulVecLin_apply, hgpHX_mulVec_apply, Matrix.mul_apply, Matrix.mul_apply]
  rfl
end QECCertificates
