-- Prove2me | solution 1 for QECCertificates.finrank_rowsSub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:24.112468+00:00
-- url     : https://prove2.me/submissions/c2d19aca-4737-44ef-9ce1-48c77f5e9d08

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
theorem _root_.solution (W : Submodule (ZMod 2) (Vec s)) :
    Module.finrank (ZMod 2) (rowsSub (p := p) W) = p * Module.finrank (ZMod 2) W := by
  rw [(rowsSubEquiv (p := p) W).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  simp
end QECCertificates
