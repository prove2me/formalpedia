-- Prove2me | solution 1 for QECCertificates.reduceAgainst_self_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:46.009108+00:00
-- url     : https://prove2.me/submissions/7dd79d2b-70e8-4230-b837-d48338604628

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
public import Theorems.Thm_QECCertificates_reduceAgainst_zero
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_reduceAgainst_cons
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
theorem _root_.solution {D : List (PivRow n)} (hD : IsReduced D) {ri : PivRow n}
    (hri : ri ∈ D) : reduceAgainst D ri.1 = 0 := by
  induction D with
  | nil => exact absurd hri (by simp)
  | cons r D ih =>
      rw [reduceAgainst_cons]
      rcases List.mem_cons.mp hri with h_eq | h_mem
      · rw [h_eq, hD.1 r (List.mem_cons_self ..), one_smul, add_self]
        exact reduceAgainst_zero D
      · by_cases hr : ri = r
        · rw [hr, hD.1 r (List.mem_cons_self ..), one_smul, add_self]
          exact reduceAgainst_zero D
        · have hD' : IsReduced D :=
            ⟨fun rj hrj => hD.1 rj (List.mem_cons_of_mem r hrj),
             fun rj hrj rk hrk hne =>
               hD.2 rj (List.mem_cons_of_mem r hrj) rk (List.mem_cons_of_mem r hrk) hne⟩
          rw [hD.2 ri (List.mem_cons_of_mem r h_mem) r (List.mem_cons_self ..) hr, zero_smul,
            add_zero]
          exact ih hD' h_mem
end QECCertificates
