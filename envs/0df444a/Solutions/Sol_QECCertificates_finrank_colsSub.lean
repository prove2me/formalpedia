-- Prove2me | solution 1 for QECCertificates.finrank_colsSub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:21.170514+00:00
-- url     : https://prove2.me/submissions/31c22f92-1762-40ac-a6a8-165b5627482e

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore
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
open _root_.Matrix
open scoped BigOperators
variable {p q r s a b : ℕ}
namespace QECCertificates
theorem _root_.solution (U : Submodule (ZMod 2) (Vec p)) :
    Module.finrank (ZMod 2) (colsSub (s := s) U) = s * Module.finrank (ZMod 2) U := by
  rw [(colsSubEquiv (s := s) U).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  simp
end QECCertificates
