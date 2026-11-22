-- Prove2me | solution 1 for QECCertificates.LRAT.slotVar_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:15:06.395569+00:00
-- url     : https://prove2.me/submissions/fa5c6527-b2a7-4cd6-a45c-4d77820b822f

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_LRAT
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Theorems.Thm_QECCertificates_LRAT_dotS_nil
public import Theorems.Thm_QECCertificates_LRAT_dotS_cons
public import Theorems.Thm_QECCertificates_LRAT_cntS_nil
attribute [local simp] QECCertificates.LRAT.dotS_nil
attribute [local simp] QECCertificates.LRAT.dotS_cons
attribute [local simp] QECCertificates.LRAT.cntS_nil

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution (c k : Nat) : SlotOK (slotVar c k) k := by
  intro i j
  by_cases h : 1 ≤ j ∧ j ≤ min i (k + 1) <;> simp [slotVar, h]
end QECCertificates.LRAT
