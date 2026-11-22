-- Prove2me | solution 1 for QECCertificates.dotProduct_e_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:04.099419+00:00
-- url     : https://prove2.me/submissions/bc8a4ce0-0f76-4525-b999-764016b8e805

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basis
public import Theorems.Thm_QECCertificates_e_dotProduct
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
theorem _root_.solution (A : List (Fin n)) (v : Vec n) :
    ((A.map e).sum) ⬝ᵥ v = (A.map v).sum := by
  induction A with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, add_dotProduct,
        e_dotProduct, ih]
end QECCertificates
