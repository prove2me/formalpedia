-- Prove2me | solution 1 for QECCertificates.lpHZ_liftConst_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:56.045211+00:00
-- url     : https://prove2.me/submissions/cc3c4fd8-ac9c-4b6e-8cb8-81461ed71aa3

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
public import Theorems.Thm_QECCertificates_lpHZ_inl
public import Theorems.Thm_QECCertificates_lpExpandL_liftConst
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_hgpHZ_inl
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
    (x : (Fin nA × Fin nB) × G) (y : (Fin nA × Fin mB) × G) :
    lpHZ (liftConst A) (liftConst B) x (Sum.inl y)
      = hgpHZ A B.transpose x.1 (Sum.inl y.1) * (if x.2 = y.2 then 1 else 0) := by
  simp only [lpHZ_inl, lpExpandL_liftConst, hgpHZ_inl, Matrix.transpose_apply]
  by_cases h : x.2 = y.2
  · simp [h]
  · simp [h, Ne.symm h]
end QECCertificates
