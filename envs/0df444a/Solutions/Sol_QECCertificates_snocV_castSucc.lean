-- Prove2me | solution 1 for QECCertificates.snocV_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:43:29.158801+00:00
-- url     : https://prove2.me/submissions/c50764e9-b5d2-432d-8ed2-b61b24b51596

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_WeightEnum
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
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {u : Vec n} {b : ZMod 2} (i : Fin n) :
    snocV u b i.castSucc = u i := by
  simp only [snocV]
  rw [dif_pos (show ((i.castSucc : Fin (n + 1)) : ℕ) < n from i.isLt)]
  exact congrArg u (Fin.ext rfl)
end QECCertificates
