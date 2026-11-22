-- Prove2me | solution 1 for QECCertificates.snocV_prefix_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:57:09.897171+00:00
-- url     : https://prove2.me/submissions/985cdb4b-012c-40c4-b972-87ef401862bc

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
public import Theorems.Thm_QECCertificates_snocV_castSucc
public import Theorems.Thm_QECCertificates_snocV_last
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support


attribute [local simp] QECCertificates.snocV_castSucc
attribute [local simp] QECCertificates.snocV_last

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (v : Vec (n + 1)) :
    snocV (fun i : Fin n => v i.castSucc) (v (Fin.last n)) = v := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, hj⟩ | hj
  · rw [hj, snocV_castSucc]
  · rw [hj, snocV_last]
end QECCertificates
