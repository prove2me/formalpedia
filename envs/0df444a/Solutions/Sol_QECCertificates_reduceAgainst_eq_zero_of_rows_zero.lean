-- Prove2me | solution 1 for QECCertificates.reduceAgainst_eq_zero_of_rows_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:51:56.903687+00:00
-- url     : https://prove2.me/submissions/6a84cfe5-9a1a-4938-90f7-28d7f3b01e2e

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Theorems.Thm_QECCertificates_reduceAgainst_cons
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} {q : Fin n} {v : Vec n}
    (hrows : ∀ ri ∈ D, ri.1 q = 0) (hv : v q = 0) : reduceAgainst D v q = 0 := by
  induction D generalizing v with
  | nil => simpa using hv
  | cons ri D ih =>
      rw [reduceAgainst_cons]
      refine ih ?_ ?_
      · intro rk hrk
        exact hrows rk (List.mem_cons_of_mem ri hrk)
      · rw [Pi.add_apply, Pi.smul_apply, hrows ri (List.mem_cons_self ..), smul_eq_mul, hv,
          mul_zero, add_zero]
end QECCertificates
