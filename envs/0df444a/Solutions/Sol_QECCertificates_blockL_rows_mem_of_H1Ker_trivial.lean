-- Prove2me | solution 1 for QECCertificates.blockL_rows_mem_of_H1Ker_trivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:36.617598+00:00
-- url     : https://prove2.me/submissions/ca1a3d13-0d59-47ef-a557-090260a69505

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
    (hT : ∀ u : Vec n₁, H₁ *ᵥ u = 0 → u = 0) (a : Fin n₁) :
    (fun b => blockL v a b) ∈ spanL (matRowList H₂) := by
  refine mem_spanL_of_forall_dot_eq_zero H₂ fun z hz => ?_
  have hzero : blockL v *ᵥ z = 0 := hT _ (by
    rw [Matrix.mulVec_mulVec, hcomp, ← Matrix.mulVec_mulVec, hz]
    simp)
  have := congrFun hzero a
  rw [dotProduct]
  exact this
end QECCertificates
