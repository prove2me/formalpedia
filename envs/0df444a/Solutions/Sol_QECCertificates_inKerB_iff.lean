-- Prove2me | solution 1 for QECCertificates.inKerB_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:46:34.554843+00:00
-- url     : https://prove2.me/submissions/0b53f513-8974-413c-a7e9-13299a27b065

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
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



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (x : Vec n) :
    inKerB M x = true ↔ x ∈ LinearMap.ker M.toLin' := by
  rw [mem_ker_iff_dotProd_rows_eq_zero]
  unfold inKerB
  rw [List.all_eq_true]
  constructor
  · intro h i
    have hmem : decide ((M i) ⬝ᵥ x = 0) ∈
        List.ofFn (fun i : Fin k => decide ((M i) ⬝ᵥ x = 0)) := by
      rw [List.mem_ofFn]; exact ⟨i, rfl⟩
    simpa using h _ hmem
  · intro h b hb
    rw [List.mem_ofFn] at hb
    obtain ⟨i, hi⟩ := hb
    rw [← hi]
    simpa using h i
end QECCertificates
