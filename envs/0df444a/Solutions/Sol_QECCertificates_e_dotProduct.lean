-- Prove2me | solution 1 for QECCertificates.e_dotProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:51:41.311029+00:00
-- url     : https://prove2.me/submissions/66e38e5f-cef8-4b4f-8357-21f9de341f31

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basis
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
theorem _root_.solution (a : Fin n) (v : Vec n) : e a ⬝ᵥ v = v a := by
  rw [dotProduct, Finset.sum_eq_single a]
  · simp [e]
  · intro b _ hb; simp [e, hb]
  · intro h; exact absurd (Finset.mem_univ a) h
end QECCertificates
