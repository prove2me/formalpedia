-- Prove2me | solution 1 for QECCertificates.dot_eq_zero_of_mem_kerL_of_mem_spanL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:05:33.717864+00:00
-- url     : https://prove2.me/submissions/e1cef2f7-396b-4d7e-8b19-c31e36794927

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
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
theorem _root_.solution {n : ℕ} {L : List (Vec n)} {z u : Vec n}
    (hz : z ∈ kerL L) (hu : u ∈ spanL L) : u ⬝ᵥ z = 0 := by
  refine Submodule.span_induction (p := fun u _ => u ⬝ᵥ z = 0) ?_ ?_ ?_ ?_ hu
  · intro v hv
    exact (mem_kerL.mp hz) v hv
  · simp
  · intro x y _ _ hx hy
    rw [add_dotProduct, hx, hy, add_zero]
  · intro c x _ hx
    rw [smul_dotProduct, hx, smul_zero]
end QECCertificates
