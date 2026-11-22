-- Prove2me | solution 1 for QECCertificates.lpExpandR_liftConst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:43.975848+00:00
-- url     : https://prove2.me/submissions/a2f7fd5d-bf37-47d6-91af-c6a1b2b9046a

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_LiftedProduct
public import Theorems.Thm_QECCertificates_mul_inv_eq_one_iff
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
theorem _root_.solution [DecidableEq G] {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (i : Fin m) (σ : G) (j : Fin n) (τ : G) :
    lpExpandR (liftConst A) (i, σ) (j, τ) = A i j * (if σ = τ then 1 else 0) := by
  simp only [lpExpandR, liftConst]
  by_cases h : σ = τ
  · rw [if_pos ((mul_inv_eq_one_iff σ τ).mpr h), if_pos h]
  · rw [if_neg (fun hc => h ((mul_inv_eq_one_iff σ τ).mp hc)), if_neg h]
end QECCertificates
