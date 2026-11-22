-- Prove2me | solution 1 for QECCertificates.LRAT.rowFill_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:59:52.121493+00:00
-- url     : https://prove2.me/submissions/0162054d-2127-48cc-b0c8-676ddbb7aa92

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_cntS_nil
public import Theorems.Thm_QECCertificates_LRAT_dotS_cons
public import Theorems.Thm_QECCertificates_LRAT_dotS_nil
attribute [local simp] QECCertificates.LRAT.cntS_nil
attribute [local simp] QECCertificates.LRAT.dotS_cons
attribute [local simp] QECCertificates.LRAT.dotS_nil



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {τ : Assign} {c k i cnt t : Nat}
    (h : ¬ (c + slotBase k i ≤ t ∧ t < c + slotBase k i + min i (k + 1))) :
    rowFill τ c k i cnt t = τ t := by
  simp only [rowFill]
  rw [if_neg h]
end QECCertificates.LRAT
