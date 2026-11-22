-- Prove2me | solution 1 for QECCertificates.exists_mul_eq_of_rows_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:14.380806+00:00
-- url     : https://prove2.me/submissions/b3d27eed-3493-4b1e-b69d-ae838b9b86bd

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Theorems.Thm_QECCertificates_exists_coeff_of_mem_spanL_matRowList
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_blockL_apply
public import Theorems.Thm_QECCertificates_blockR_apply
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
theorem _root_.solution {m k p : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2))
    (U : Matrix (Fin p) (Fin k) (ZMod 2))
    (h : ∀ a, (fun j => U a j) ∈ spanL (matRowList M)) :
    ∃ C : Matrix (Fin p) (Fin m) (ZMod 2), C * M = U := by
  classical
  choose c hc using fun a => exists_coeff_of_mem_spanL_matRowList M (h a)
  refine ⟨Matrix.of fun a t => c a t, ?_⟩
  ext a j
  rw [Matrix.mul_apply]
  simpa only [Matrix.of_apply] using hc a j
end QECCertificates
