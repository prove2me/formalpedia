-- Prove2me | solution 1 for QECCertificates.readOff_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:02.537914+00:00
-- url     : https://prove2.me/submissions/d98390c0-77fd-4f5a-9315-490cb5bb143d

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Theorems.Thm_QECCertificates_readOff_nil
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_kerL
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil


attribute [local simp] QECCertificates.readOff_nil

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (D : List (PivRow n)) (x y : Vec n) :
    readOff D (x + y) = readOff D x + readOff D y := by
  simp only [readOff]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ri _ => by rw [Pi.add_apply, add_smul]
end QECCertificates
