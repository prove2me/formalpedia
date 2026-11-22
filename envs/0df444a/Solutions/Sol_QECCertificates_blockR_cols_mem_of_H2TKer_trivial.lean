-- Prove2me | solution 1 for QECCertificates.blockR_cols_mem_of_H2TKer_trivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:44.74883+00:00
-- url     : https://prove2.me/submissions/23e10035-42a2-4744-9c46-48802084a44a

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Theorems.Thm_QECCertificates_mem_spanL_of_forall_dot_eq_zero
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
theorem _root_.solution
    {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)} {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)}
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hcomp : H₁ * blockL v = blockR v * H₂)
    (hT : ∀ u : Vec r₂, H₂.transpose *ᵥ u = 0 → u = 0) (t : Fin r₂) :
    (fun i => blockR v i t) ∈ spanL (colList H₁) := by
  rw [colList]
  refine mem_spanL_of_forall_dot_eq_zero H₁.transpose fun w hw => ?_
  have hyzero : H₂.transpose *ᵥ ((blockR v).transpose *ᵥ w) = 0 := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← hcomp, Matrix.transpose_mul,
      ← Matrix.mulVec_mulVec, hw]
    simp
  have hy := hT _ hyzero
  have hy' : ∀ t, ((blockR v).transpose *ᵥ w) t = 0 := fun t => by
    simpa using congrFun hy t
  rw [dotProduct]
  exact hy' t
end QECCertificates
