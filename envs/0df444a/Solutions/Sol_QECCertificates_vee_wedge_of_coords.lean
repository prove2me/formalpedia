-- Prove2me | solution 1 for QECCertificates.vee_wedge_of_coords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:52.231043+00:00
-- url     : https://prove2.me/submissions/fe9cfa62-c7d9-4886-8e08-ca4f0eae2f32

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
    {U : Submodule (ZMod 2) (Vec p)}
    (hcoords : ∀ x ∈ U, ∑ k, L x k • u k = x) {X : VMat p s} (hX : ∀ j, colOf X j ∈ U) :
    vee u (wedge L X) = X := by
  ext ⟨i, j⟩
  simp only [vee_apply, wedge_apply]
  have h := congrFun (hcoords (colOf X j) (hX j)) i
  simpa using h
end QECCertificates
