-- Prove2me | solution 1 for QECCertificates.LinearMap.ker_eq_kerL_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:15.66773+00:00
-- url     : https://prove2.me/submissions/6798b6a8-601d-4670-9718-ba7a7ebc4d0d

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_ker_iff_dotProd_rows_eq_zero
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil


attribute [local simp] QECCertificates.mem_kerL

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
namespace LinearMap
theorem _root_.solution {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    LinearMap.ker M.toLin' = kerL (List.ofFn fun i => M i) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [mem_kerL]
    rw [mem_ker_iff_dotProd_rows_eq_zero] at hx
    intro r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact hx i
  · intro x hx
    rw [mem_ker_iff_dotProd_rows_eq_zero]
    intro i
    exact (mem_kerL.mp hx) (M i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
end LinearMap
end QECCertificates
