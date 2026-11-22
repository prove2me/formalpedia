-- Prove2me | solution 1 for QECCertificates.linearMap_apply_eq_sum_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:31.842286+00:00
-- url     : https://prove2.me/submissions/44b6e1e0-b383-43b9-81f7-581668e18175

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore
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
open _root_.Matrix
open scoped BigOperators
variable {p q r s a b : ℕ}
namespace QECCertificates
theorem _root_.solution (L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)) (x : Vec p) :
    L x = fun k => ∑ i, x i * L (Pi.single i (1 : ZMod 2)) k := by
  conv_lhs => rw [show x = ∑ i, x i • (Pi.single i (1 : ZMod 2)) from by
    funext j
    simp [Pi.single_apply]]
  funext k
  simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
end QECCertificates
