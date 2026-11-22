-- Prove2me | solution 1 for QECCertificates.LRAT.chainAssign_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:43:46.204452+00:00
-- url     : https://prove2.me/submissions/684edcdb-04da-4add-918f-a452b9a37942

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
theorem _root_.solution {σ : Assign} {rest : List Nat} {acc : Bool} {c t : Nat}
    (h : t < c) : chainAssign σ rest acc c t = σ t := by
  simp only [chainAssign, h, ite_true]
end QECCertificates.LRAT
