-- Prove2me | solution 1 for QECCertificates.lpExpandL_liftConst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:08.044215+00:00
-- url     : https://prove2.me/submissions/8597f756-4387-484f-aab0-6986f9c7a9f1

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
public import Theorems.Thm_QECCertificates_inv_mul_eq_one_iff
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
theorem _root_.solution [DecidableEq G] {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (s : Fin m) (σ : G) (t : Fin n) (τ : G) :
    lpExpandL (liftConst B) (s, σ) (t, τ) = B s t * (if σ = τ then 1 else 0) := by
  simp only [lpExpandL, liftConst]
  by_cases h : σ = τ
  · rw [if_pos ((inv_mul_eq_one_iff σ τ).mpr h), if_pos h]
  · rw [if_neg (fun hc => h ((inv_mul_eq_one_iff σ τ).mp hc)), if_neg h]
end QECCertificates
