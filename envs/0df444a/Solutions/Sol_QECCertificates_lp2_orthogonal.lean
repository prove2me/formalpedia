-- Prove2me | solution 1 for QECCertificates.lp2_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:33.121906+00:00
-- url     : https://prove2.me/submissions/8aaa4f91-a9aa-481f-bd4e-fb9453b781e3

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
public import Theorems.Thm_QECCertificates_leftMulMat_mul_rightMulMat
public import Theorems.Thm_QECCertificates_lp2HX_inl
public import Theorems.Thm_QECCertificates_lp2HX_inr
public import Theorems.Thm_QECCertificates_lp2HZ_inl
public import Theorems.Thm_QECCertificates_lp2HZ_inr
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
variable {G : Type*} [Group G]
namespace QECCertificates
theorem _root_.solution [Fintype G] (a b : G → ZMod 2) :
    lp2HX a b * (lp2HZ a b).transpose = 0 := by
  ext σ σ'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, Fintype.sum_sum_type,
    lp2HX_inl, lp2HX_inr, lp2HZ_inl, lp2HZ_inr]
  rw [← Matrix.mul_apply, ← Matrix.mul_apply, leftMulMat_mul_rightMulMat]
  exact CharTwo.add_self_eq_zero _
end QECCertificates
