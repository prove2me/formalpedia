-- Prove2me | solution 1 for QECCertificates.lpHX_liftConst_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:57.934518+00:00
-- url     : https://prove2.me/submissions/caed1bd4-64b2-4681-8169-5645ae5618ec

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
public import Theorems.Thm_QECCertificates_lpHX_inr
public import Theorems.Thm_QECCertificates_lpExpandL_liftConst
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_hgpHX_inr
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
    (x : (Fin mA × Fin mB) × G) (y : (Fin mA × Fin nB) × G) :
    lpHX (liftConst A) (liftConst B) x (Sum.inr y)
      = hgpHX A B.transpose x.1 (Sum.inr y.1) * (if x.2 = y.2 then 1 else 0) := by
  simp only [lpHX_inr, lpExpandL_liftConst, hgpHX_inr, Matrix.transpose_apply]
  by_cases h : x.2 = y.2
  · simp [h]
  · simp [h]
end QECCertificates
