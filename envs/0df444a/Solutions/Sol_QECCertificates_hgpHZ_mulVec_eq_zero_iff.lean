-- Prove2me | solution 1 for QECCertificates.hgpHZ_mulVec_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:59.846695+00:00
-- url     : https://prove2.me/submissions/7f2ff9a7-56e3-43d7-917b-77be52adc9e8

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGP
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Theorems.Thm_QECCertificates_blockL_apply
public import Theorems.Thm_QECCertificates_blockR_apply
public import Theorems.Thm_QECCertificates_hgpHZ_mulVec_apply
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_eq_zero_iff_eq
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support


attribute [local simp] QECCertificates.blockL_apply
attribute [local simp] QECCertificates.blockR_apply

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}
namespace QECCertificates
theorem _root_.solution (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    (v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2) :
    hgpHZ H₁ H₂ *ᵥ v = 0 ↔ blockL v * H₂.transpose = H₁.transpose * blockR v := by
  constructor
  · intro hv
    funext a d
    have h := congrFun hv (a, d)
    rw [hgpHZ_mulVec_apply] at h
    simp only [Pi.zero_apply] at h
    exact (add_eq_zero_iff_eq _ _).mp h
  · intro hcomp
    funext x
    obtain ⟨a, d⟩ := x
    rw [hgpHZ_mulVec_apply, hcomp]
    simp only [Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
end QECCertificates
