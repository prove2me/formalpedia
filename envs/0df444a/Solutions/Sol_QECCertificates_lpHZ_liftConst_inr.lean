-- Prove2me | solution 1 for QECCertificates.lpHZ_liftConst_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:58.307602+00:00
-- url     : https://prove2.me/submissions/5344b244-082c-43b3-a22f-f4c41add7ad8

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
public import Theorems.Thm_QECCertificates_lpHZ_inr
public import Theorems.Thm_QECCertificates_lpExpandR_liftConst
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_hgpHZ_inr
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
    (x : (Fin nA × Fin nB) × G) (y : (Fin mA × Fin nB) × G) :
    lpHZ (liftConst A) (liftConst B) x (Sum.inr y)
      = hgpHZ A B.transpose x.1 (Sum.inr y.1) * (if x.2 = y.2 then 1 else 0) := by
  simp only [lpHZ_inr, lpExpandR_liftConst, hgpHZ_inr]
  by_cases h : x.2 = y.2
  · simp [h]
  · simp [h, Ne.symm h]
end QECCertificates
