-- Prove2me | solution 1 for QECCertificates.leadIdx_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:48:14.544654+00:00
-- url     : https://prove2.me/submissions/2c6404a8-a476-407f-a393-30da592678a0

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
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
theorem _root_.solution (v : Vec n) (h : v ≠ 0) : v (leadIdx v h) ≠ 0 := by
  unfold leadIdx
  have hm := Finset.min'_mem (Finset.univ.filter (fun i => v i ≠ 0)) (support_nonempty h)
  simpa using hm
end QECCertificates
