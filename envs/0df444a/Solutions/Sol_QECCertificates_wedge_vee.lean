-- Prove2me | solution 1 for QECCertificates.wedge_vee
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:56.993919+00:00
-- url     : https://prove2.me/submissions/deb77820-b1a3-413e-96ef-f6c657f42b37

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore
public import Theorems.Thm_QECCertificates_vee_apply
public import Theorems.Thm_QECCertificates_wedge_apply
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support


attribute [local simp] QECCertificates.vee_apply
attribute [local simp] QECCertificates.wedge_apply

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {p q r s a b : ℕ}
namespace QECCertificates
theorem _root_.solution {u : Fin a → Vec p} {L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)}
    (hleft : ∀ c : Fin a → ZMod 2, L (∑ k, c k • u k) = c) (C : VMat a s) :
    wedge L (vee u C) = C := by
  ext ⟨k, j⟩
  simp only [wedge_apply]
  have hcol : colOf (vee u C) j = ∑ k', C (k', j) • u k' := by
    funext i
    rw [colOf_apply, vee_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [Pi.smul_apply, smul_eq_mul]
  rw [hcol, hleft]
end QECCertificates
