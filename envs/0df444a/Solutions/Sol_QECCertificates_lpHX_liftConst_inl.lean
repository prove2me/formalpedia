-- Prove2me | solution 1 for QECCertificates.lpHX_liftConst_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:46.761846+00:00
-- url     : https://prove2.me/submissions/3efd7b58-206c-4000-8758-b4af4817bb08

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
public import Theorems.Thm_QECCertificates_lpHX_inl
public import Theorems.Thm_QECCertificates_lpExpandR_liftConst
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_hgpHX_inl
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {G : Type*} [Group G]
namespace QECCertificates
theorem _root_.solution [DecidableEq G] {mA nA mB nB : ℕ} (A : Matrix (Fin mA) (Fin nA) (ZMod 2))
    (B : Matrix (Fin mB) (Fin nB) (ZMod 2))
    (x : (Fin mA × Fin mB) × G) (y : (Fin nA × Fin mB) × G) :
    lpHX (liftConst A) (liftConst B) x (Sum.inl y)
      = hgpHX A B.transpose x.1 (Sum.inl y.1) * (if x.2 = y.2 then 1 else 0) := by
  simp only [lpHX_inl, lpExpandR_liftConst, hgpHX_inl]
  by_cases h : x.2 = y.2
  · simp [h]
  · simp [h]
end QECCertificates
