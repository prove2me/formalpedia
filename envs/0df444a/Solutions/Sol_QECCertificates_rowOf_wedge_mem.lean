-- Prove2me | solution 1 for QECCertificates.rowOf_wedge_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:08.644627+00:00
-- url     : https://prove2.me/submissions/87862cb1-19fa-4489-8eef-281238bab901

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore
public import Theorems.Thm_QECCertificates_linearMap_apply_eq_sum_single
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
theorem _root_.solution {L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)}
    {W : Submodule (ZMod 2) (Vec s)} {X : VMat p s} (hX : ∀ i, rowOf X i ∈ W) :
    ∀ k, rowOf (wedge L X) k ∈ W := by
  intro k
  have hrow : rowOf (wedge L X) k = ∑ i : Fin p, (L (Pi.single i (1 : ZMod 2)) k) • rowOf X i := by
    funext j
    rw [rowOf_apply, wedge_apply, linearMap_apply_eq_sum_single L (colOf X j)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rowOf_apply, colOf_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [hrow]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hX i)
end QECCertificates
