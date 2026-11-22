-- Prove2me | solution 1 for QECCertificates.rowOf_mem_of_wedge_rowOf_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:00.496801+00:00
-- url     : https://prove2.me/submissions/ac484bce-08eb-4ff2-9cec-5261c54184fc

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore
public import Theorems.Thm_QECCertificates_vee_apply
public import Theorems.Thm_QECCertificates_wedge_apply
public import Theorems.Thm_QECCertificates_vee_wedge_of_coords
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
    {U : Submodule (ZMod 2) (Vec p)} {W : Submodule (ZMod 2) (Vec s)}
    (hcoords : ∀ x ∈ U, ∑ k, L x k • u k = x) {X : VMat p s}
    (hX : ∀ j, colOf X j ∈ U) (hY : ∀ k, rowOf (wedge L X) k ∈ W) :
    ∀ i, rowOf X i ∈ W := by
  intro i
  have hrow : rowOf X i = ∑ k, (u k i) • rowOf (wedge L X) k := by
    funext j
    have h := congrFun (vee_wedge_of_coords hcoords hX) (i, j)
    simp only [vee_apply, wedge_apply, rowOf_apply] at h ⊢
    rw [← h]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rowOf_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hrow]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hY k)
end QECCertificates
